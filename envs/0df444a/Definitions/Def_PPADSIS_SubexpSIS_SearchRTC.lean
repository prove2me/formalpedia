-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_SearchRTC
-- name    : PPADSIS_SubexpSIS_SearchRTC
-- status  : Definition
-- author  : @arka
-- created : 2026-11-13T05:38:24.198099+00:00
-- url     : https://prove2.me/theorems/9d6426eb-9284-4e39-80d2-1e5de1e7ff74
-- title:
--   Exhaustive search as a regular tree circuit (the map $\Phi$ of Lemma 3.9)
-- statement:
--   Let $\varphi:\{0,1\}^n\to\{0,1\}$ be a Boolean circuit with one output. The **exhaustive-search tree circuit** $\Phi(\varphi)$ is the regular tree circuit (Definition 3.8) $C=(p,C_0,C_1,\dots,C_p)$ with address length $p=n$ and the following circuits.
--
--   1. The leaf circuit $C_0:\{0,1\}^n\to\{0,1\}^{n+1}$ evaluates $\varphi$ and masks the address by the result:
--   $$C_0(a)=\bigl(\varphi(a),\ a_0\wedge\varphi(a),\ \dots,\ a_{n-1}\wedge\varphi(a)\bigr).$$
--   It consists of the gates of $\varphi$ followed by $n$ conjunctions.
--   2. Every combining circuit $C_h:\{0,1\}^{2(n+1)}\to\{0,1\}^{n+1}$, $h\in[p]$, is the same circuit. On a left value $(f_L,a_L)$ and a right value $(f_R,a_R)$ it outputs
--   $$C_h(f_L,a_L,f_R,a_R)=\bigl(f_L\vee f_R,\ a_L\vee(\neg f_L\wedge a_R)\bigr),$$
--   with the disjunction and conjunction taken bitwise. It has $2n+2$ gates: $\neg f_L$, $f_L\vee f_R$, then $\neg f_L\wedge a_{R,i}$ and $a_{L,i}\vee(\neg f_L\wedge a_{R,i})$ for each $i<n$.
--
--   Every node therefore carries a flag and an address. The flag says whether some leaf below it satisfies $\varphi$, and the address is the leftmost such leaf, or $0^n$ if there is none. Because the left child of a node holds the lexicographically smaller addresses, the root outputs the result of exhaustive search for the lexicographically first satisfying assignment, as in Lemma 3.9.
--
--   **Formalization Note** The output wire of $\varphi$ is read as the head of `φ.outs` (wire $0$ if there is none), and the definition is total on all circuits. Its correctness and size bound are the separate theorem `PPADSIS.SubexpSIS.searchRTC_spec`; its polynomial-time computability is `PPADSIS.SubexpSIS.searchRTC_polyTime`.
-- source:
--   Arka Rai Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript), Lemma 3.9 and Definition 3.8, p. 22

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_RegularTreeCircuit

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

namespace SearchRTC

/-- The output wire of `φ` (its only one, for a one-output circuit). -/
def outWire (φ : Circuit) : ℕ := φ.outs.headD 0

/-- Leaf circuit `C₀(a) = (φ(a), a ∧ φ(a))`: the gates of `φ`, then `a_i ∧ φ(a)` for each `i`. -/
def leafC (φ : Circuit) : Circuit :=
  ⟨φ.nIn, φ.gates ++ (List.range φ.nIn).map (fun i => Gate.and (outWire φ) i),
    outWire φ :: (List.range φ.nIn).map (fun i => φ.nIn + φ.gates.length + i)⟩

/-- Gate `k` of the combining circuit on inputs `(f_L, a_L, f_R, a_R)` (wires `0`, `1..n`, `n+1`,
`n+2..2n+1`): `¬f_L`, `f_L ∨ f_R`, then `¬f_L ∧ a_R,i`, then `a_L,i ∨ (¬f_L ∧ a_R,i)`. -/
def combGate (n k : ℕ) : Gate :=
  if k = 0 then .not 0
  else if k = 1 then .or 0 (n + 1)
  else if k < n + 2 then .and (2 * n + 2) (n + k)
  else .or (k - n - 1) (n + 2 + k)

/-- Combining circuit `(f_L, a_L, f_R, a_R) ↦ (f_L ∨ f_R, a_L ∨ (¬f_L ∧ a_R))`. -/
def combC (n : ℕ) : Circuit :=
  ⟨2 * n + 2, (List.range (2 * n + 2)).map (combGate n),
    (2 * n + 3) :: (List.range n).map (fun i => 3 * n + 4 + i)⟩

end SearchRTC

open SearchRTC in
/-- **Exhaustive search as a regular tree circuit** (Choudhuri, *PPAD Hardness from SIS*, STOC 2027
submission, Lemma 3.9, p. 22): for a one-output circuit `φ` on `n = φ.nIn` inputs, the regular tree
circuit of address length `n` whose leaf circuit is `C₀(a) = (φ(a), a ∧ φ(a))` and whose combining
circuit at every height is `(f_L, a_L, f_R, a_R) ↦ (f_L ∨ f_R, a_L ∨ (¬f_L ∧ a_R))`. -/
def searchRTC (φ : Circuit) : RTC :=
  ⟨φ.nIn, leafC φ, List.replicate φ.nIn (combC φ.nIn)⟩

end PPADSIS.SubexpSIS


