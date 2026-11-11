-- Prove2me | Definitions.Def_OptAbstention_TLA_SelectorIO
-- name    : OptAbstention_TLA_SelectorIO
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:08:05.839536+00:00
-- url     : https://prove2.me/theorems/8724870f-70f7-4c6e-819b-45ec72077821
-- title:
--   Input and output layouts of the selector algorithms (Lemmas F.2, F.3) and of L1 polynomial regression (Theorem 6.2)
-- statement:
--   A **selector algorithm** receives $|S|$, $|S'|$ and $\ell$ in pointers 0–2, $B,\varepsilon,\eta,\delta$ in cells 0–3, then the records of $S$ and of $S'$, each record being the $d$ coordinates of a point followed by the value $h(x)$ of the classifier at that point. Its output is $g_j$ in cell $-1-j$, valid when every $g_j\in\{0,1\}$.
--
--   The **regression algorithm** starts on empty memory and outputs a polynomial threshold function $x\mapsto\mathrm{sign}(p(x)-t)$, $\mathrm{sign}(0)=+1$: cell 0 holds the number $K$ of terms, cell 1 holds $t$, and term $j$ occupies $d+1$ cells (its exponents, natural numbers summing to at most $\ell$, then its coefficient).
--
--   **Formalization Note.** A machine cannot receive a function as input, so $h$ is given by its values at the points where the algorithm uses it.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 13, Theorem 6.2; p. 49, Lemma F.2; p. 51, Lemma F.3

import Mathlib
import Definitions.Def_OptAbstention_TLA_Machine

/-!
# Input and output layouts of the selector algorithms (Lemmas F.2, F.3) and of L1 regression
(Theorem 6.2)

Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, *Achieving the Optimal Abstention Rate
for Learning with Distribution Shift*, STOC 2027 submission (manuscript sha256 0fb30af1…),
Theorem 6.2 (p. 13), Lemma F.2 (p. 49), Lemma F.3 (p. 51).

Encoding.
* Selector input ("takes h, S, S′, ℓ, B, ε, η (, δ) as input"): pointer `0` holds `m = |S|`,
  pointer `1` holds `n′ = |S′|`, pointer `2` holds `ℓ`; cells `0, 1, 2, 3` hold `B, ε, η, δ`;
  from cell `4` on, `m` records of width `d + 1` (the coordinates of the `i`-th point of `S`, then
  `h` of it), then `n′` records of width `d + 1` for `S′`. A machine cannot receive the function
  `h`; it receives `h` at the points where it is used. Lemma F.2's algorithm takes no `δ`: its `δ` cell holds `0`.
* Selector output: `g_j` in cell `−1 − j`; valid when every `g_j ∈ {0, 1}`.
* Regression output (Theorem 6.2: the degree-`ℓ` L1 polynomial regression algorithm outputs a
  polynomial threshold function `x ↦ sign(p(x) − t)`, `sign(0) := +1`): cell `0` holds the number
  `K` of terms, cell `1` holds `t`; term `j < K` occupies cells `2 + j(d+1), …, 2 + j(d+1) + d`:
  the `d` exponents (natural numbers with sum at most `ℓ`), then the coefficient.
-/

namespace OptAbstention.TLA

/-- The start state of a selector algorithm. -/
noncomputable def selectorInit {d : ℕ} {m n : ℕ} (ℓ : ℕ) (B ε η δ : ℝ) (S : Fin m → Pt d)
    (hS : Fin m → ℝ) (S' : Fin n → Pt d) (hS' : Fin n → ℝ) : State :=
  initState (fun j => if j = 0 then (m : ℤ) else if j = 1 then (n : ℤ) else
      if j = 2 then (ℓ : ℤ) else 0)
    (blockMem 4 (d + 1) m (fun i j => if h : (j : ℕ) < d then S i ⟨j, h⟩ else hS i)
      (blockMem (4 + (m : ℤ) * (d + 1)) (d + 1) n
        (fun i j => if h : (j : ℕ) < d then S' i ⟨j, h⟩ else hS' i)
        fun c => if c = 0 then B else if c = 1 then ε else if c = 2 then η else
          if c = 3 then δ else 0))

/-- The selector value `g_j` in a final state. -/
def outSel (S : State) (j : ℕ) : ℝ := S.cfg.mem (-1 - (j : ℤ))

/-- The output block is a selector `g ∈ {0, 1}^{n}`. -/
def ValidSelector (S : State) (n : ℕ) : Prop :=
  ∀ j < n, outSel S j = 0 ∨ outSel S j = 1

/-- The start state of the regression algorithm (no input: all registers and cells `0`). -/
def emptyInit : State :=
  initState (fun _ => 0) fun _ => 0

/-- The address of field `i` of term `j` of a regression output in dimension `d`. -/
def ptfCell (d j i : ℕ) : ℤ := 2 + (j : ℤ) * (d + 1) + i

/-- The output memory encodes a degree-`ℓ` polynomial threshold function: the number of terms
and every exponent are natural numbers, and every term has total degree at most `ℓ`. -/
def ValidPTF (d ℓ : ℕ) (mem : ℤ → ℝ) : Prop :=
  ∃ K : ℕ, mem 0 = K ∧ ∀ j < K, (∀ i < d, ∃ a : ℕ, mem (ptfCell d j i) = a) ∧
    ∑ i ∈ Finset.range d, mem (ptfCell d j i) ≤ ℓ

/-- The value `p(x) − t` of the encoded polynomial threshold. -/
noncomputable def ptfValue (d : ℕ) (mem : ℤ → ℝ) (x : Pt d) : ℝ :=
  (∑ j ∈ Finset.range ⌊mem 0⌋₊,
    mem (ptfCell d j d) * ∏ i : Fin d, x i ^ ⌊mem (ptfCell d j i)⌋₊) - mem 1

/-- The encoded classifier `x ↦ sign(p(x) − t)` with `sign(0) = +1`. -/
noncomputable def ptfClassifier (d : ℕ) (mem : ℤ → ℝ) (x : Pt d) : ℝ :=
  if 0 ≤ ptfValue d mem x then 1 else -1

end OptAbstention.TLA


