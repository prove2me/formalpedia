-- Prove2me | Definitions.Def_MFOTLMon_Monitor_Constructions
-- name    : MFOTLMon_Monitor_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:51.814134+00:00
-- url     : https://prove2.me/theorems/8d73cfef-f64c-443d-8ca9-2ee591ec76a1
-- title:
--   §3.3–§3.4, pp. 15:9–15:13 — the transformed formula φ̂ over the extended signature and the incremental constructions of p_α, r_α, s_α (until repaired)
-- statement:
--   This file formalizes the signature extension of §3.3 and the incremental constructions of §3.4.
--
--   **Extended structures and $\hat\varphi$** (§3.3). The extended signature $\hat S$ adds, for each temporal subformula $\alpha$, an auxiliary predicate $p_\alpha$ of arity $n=|\mathit{free}(\alpha)|$. The formula $\hat\varphi$ is $\varphi$ with every top-level temporal subformula $\alpha$ replaced by the atom $p_\alpha(\bar x)$, $\bar x$ the vector of free variables of $\alpha$. Given relations for the predicates of $R$ (for $\hat{\mathcal D}_i$: those of $\mathcal D_i$), the constants, and relations $P(\alpha)$ for the $p_\alpha$, `hatSet` is the set $\hat\varphi^{\hat{\mathcal D}}$ of tuples satisfying $\hat\varphi$, ordinary first-order satisfaction in which $p_\alpha(\bar x)$ holds iff $(v(x_1),\dots,v(x_n))\in P(\alpha)$.
--
--   **Previous and next** (§3.4.1–3.4.2). For $\alpha=\bullet_I\beta$: $p_\alpha^{\hat{\mathcal D}_i}=\hat\beta^{\hat{\mathcal D}_{i-1}}$ if $i>0$ and $\tau_i-\tau_{i-1}\in I$, and $\emptyset$ otherwise. For $\alpha=\circ_I\beta$: $p_\alpha^{\hat{\mathcal D}_i}=\hat\beta^{\hat{\mathcal D}_{i+1}}$ if $\tau_{i+1}-\tau_i\in I$, and $\emptyset$ otherwise.
--
--   **Since** (§3.4.3), $\alpha=\beta\,\mathsf S_{[b,b')}\,\gamma$. $r_\alpha^{\hat{\mathcal D}_i}=N\cup U$ with $N=\hat\gamma^{\hat{\mathcal D}_i}\times\{0\}$, $U=\emptyset$ for $i=0$ and, for $i>0$,
--   $$
--   U=\{(\bar a,t)\mid \bar a\in\hat\beta^{\hat{\mathcal D}_i},\ t<b',\ (\bar a,t')\in r_\alpha^{\hat{\mathcal D}_{i-1}} \text{ with } t=t'+(\tau_i-\tau_{i-1})\},
--   $$
--   and $p_\alpha^{\hat{\mathcal D}_i}=\{\bar a\mid(\bar a,t)\in r_\alpha^{\hat{\mathcal D}_i}\text{ for some }t\ge b\}$.
--
--   **Until** (§3.4.4), $\alpha=\beta\,\mathsf U_{[b,b')}\,\gamma$ with $b'\in\mathbb N$. The lookahead offset is $\ell_i=\max\{j\mid\tau_{i+j}-\tau_i<b'\}$, with $\ell_{-1}:=0$. Then $r_\alpha^{\hat{\mathcal D}_i}=N_r\cup U_r$ and $s_\alpha^{\hat{\mathcal D}_i}=N_s\cup U_s\cup E_s$, where ($j\ominus1=\max\{0,j-1\}$)
--   $$
--   \begin{aligned}
--   N_r&=\{(\bar a,j)\mid \ell_{i-1}\le j\le\ell_i,\ \bar a\in\hat\beta^{\hat{\mathcal D}_{i+k}}\ \forall k\in[j,\ell_i]\},\\
--   U_r&=\{(\bar a,j\ominus1)\mid (\bar a,j)\in r_\alpha^{\hat{\mathcal D}_{i-1}},\ \bar a\in\hat\beta^{\hat{\mathcal D}_{i+k}}\ \forall k\in[\ell_{i-1},\ell_i]\},\\
--   N_s&=\{(\bar a,j,j',t)\mid \ell_{i-1}\le j\le j'\le\ell_i,\ \bar a\in\hat\gamma^{\hat{\mathcal D}_{i+j'}},\ t=\tau_{i+j'}-\tau_i\ge b,\ \bar a\in\hat\beta^{\hat{\mathcal D}_{i+k}}\ \forall k\in[j,j')\},\\
--   U_s&=\{(\bar a,j\ominus1,j'\ominus1,t)\mid (\bar a,j,j',t')\in s_\alpha^{\hat{\mathcal D}_{i-1}},\ j'\ge1,\ t+(\tau_i-\tau_{i-1})=t',\ t\ge b\},\\
--   E_s&=\{(\bar a,j\ominus1,j',t)\mid (\bar a,j)\in r_\alpha^{\hat{\mathcal D}_{i-1}},\ (\bar a,\ell_{i-1},j',t)\in N_s\},
--   \end{aligned}
--   $$
--   with $U_r=U_s=E_s=\emptyset$ for $i=0$, and $p_\alpha^{\hat{\mathcal D}_i}=\{\bar a\mid(\bar a,0,j',t)\in s_\alpha^{\hat{\mathcal D}_i}\text{ for some }j',t\}$.
--
--   Each construction is a function of its input relations ($\hat\beta$, $\hat\gamma$ at the relevant time points and the previous $r_\alpha$, $s_\alpha$), so that the monitor can apply it to stored relations and the lemmas of §3.4 can be stated about it.
--
--   **Formalization Note.** Two repairs of the printed until construction (p. 15:13) are built in. (R1) The printed guard of $U_r$ is "$(\bar a,\ell_{i-1})\in N_r$"; it is empty whenever $\ell_{i-1}=\ell_i+1$, which in the paper's own example (§3.5: $\ell_0=3$, $\ell_1=2$) gives $r_\alpha^{\hat{\mathcal D}_1}=\emptyset$ instead of the reported $\mathbb N\times\{0,1,2\}$; it is replaced by "$\bar a\in\hat\beta^{\hat{\mathcal D}_{i+k}}$ for all $\ell_{i-1}\le k\le\ell_i$", which reproduces the example. (R2) $U_s$ keeps only tuples with $j'\ge1$: a printed tuple $(\bar a,0,0,t')$ records $\gamma$ at time point $i-1$ and, when $\tau_i=\tau_{i-1}$ and $b=0$, would survive as a false witness at $i$. (R3) The printed "$t'=t-\tau_i+\tau_{i-1}$" and "$t=t'-(\tau_i-\tau_{i-1})$" are equations, encoded additively, never with truncated subtraction. The lookahead is the least $m$ with $\tau_{i+m}-\tau_i\ge b'$, minus one (it exists since $\bar\tau$ makes progress). Pairs and quadruples are lists $\bar a\mathbin{+\!\!+}[t]$ and $\bar a\mathbin{+\!\!+}[j,j',t]$. The until construction reads $b'$ as the natural number `I.hi.toNat`; it is only used for finite $b'$.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), pp. 15:9–15:13, §3.3 (extended signature, φ̂) and §3.4.1–§3.4.4 (incremental constructions; §3.4.4 repaired)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Automatic

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature}

/-- First-order satisfaction of the transformed formula `φ̂` (§3.3, p. 15:10) in an extended structure
`D̂` over `Ŝ`: the predicates of `R` are interpreted by `rels`, the constants by `const`, and the
auxiliary predicate `p_α` of a temporal formula `α` by `P α`. `φ̂` is `φ` with every top-level temporal
subformula `α` replaced by the atom `p_α(x̄)`, `x̄` the vector of free variables of `α`; so the clause
for a temporal `α` reads `(v(x₁), …, v(xₙ)) ∈ P α` and never looks inside `α`. -/
def ExtSat (rels : S.R → Set (List ℕ)) (const : S.C → ℕ) (P : Formula S → Set (List ℕ)) :
    Formula S → (ℕ → ℕ) → Prop
  | .eq t t', v => evalTerm const v t = evalTerm const v t'
  | .pred r ts, v => List.ofFn (fun k => evalTerm const v (ts k)) ∈ rels r
  | .neg ψ, v => ¬ ExtSat rels const P ψ v
  | .or ψ ψ', v => ExtSat rels const P ψ v ∨ ExtSat rels const P ψ' v
  | .ex x ψ, v => ∃ d : ℕ, ExtSat rels const P ψ (Function.update v x d)
  | .prev I ψ, v => (freeList (.prev I ψ)).map v ∈ P (.prev I ψ)
  | .next I ψ, v => (freeList (.next I ψ)).map v ∈ P (.next I ψ)
  | .since I ψ ψ', v => (freeList (.since I ψ ψ')).map v ∈ P (.since I ψ ψ')
  | .until I ψ ψ', v => (freeList (.until I ψ ψ')).map v ∈ P (.until I ψ ψ')

/-- The set `φ̂^{D̂}` of tuples (in the order `freeList φ`) satisfying `φ̂` in the extended structure
given by `rels`, `const` and the auxiliary relations `P`. -/
def hatSet (rels : S.R → Set (List ℕ)) (const : S.C → ℕ) (P : Formula S → Set (List ℕ))
    (φ : Formula S) : Set (List ℕ) :=
  {ds | ds.length = (freeList φ).length ∧
    ∃ v : ℕ → ℕ, ExtSat rels const P φ (assign v (freeList φ) ds)}

/-! ### §3.4.1–3.4.2: previous and next (p. 15:10–15:11) -/

/-- `p_α^{D̂ᵢ}` for `α = ●_I β`, given `Bprev = β̂^{D̂_{i−1}}`: `Bprev` if `i > 0` and
`τᵢ − τ_{i−1} ∈ I`, `∅` otherwise. -/
def prevP (τ : ℕ → ℕ) (I : Interval) (i : ℕ) (Bprev : Set (List ℕ)) : Set (List ℕ) :=
  if 0 < i ∧ I.Mem (τ i - τ (i - 1)) then Bprev else ∅

/-- `p_α^{D̂ᵢ}` for `α = ○_I β`, given `Bnext = β̂^{D̂_{i+1}}`: `Bnext` if `τ_{i+1} − τᵢ ∈ I`, `∅`
otherwise. -/
def nextP (τ : ℕ → ℕ) (I : Interval) (i : ℕ) (Bnext : Set (List ℕ)) : Set (List ℕ) :=
  if I.Mem (τ (i + 1) - τ i) then Bnext else ∅

/-! ### §3.4.3: since (p. 15:11). A pair `(ā, t)` is the list `ā ++ [t]`. -/

/-- One step of the construction of `r_α^{D̂ᵢ} = N ∪ U` for `α = β S_{[b,b′)} γ`, given
`B = β̂^{D̂ᵢ}`, `G = γ̂^{D̂ᵢ}` and `rprev = r_α^{D̂_{i−1}}`: `N = γ̂^{D̂ᵢ} × {0}`, `U = ∅` if `i = 0`,
and for `i > 0`, `U = {(ā, t) | ā ∈ β̂^{D̂ᵢ}, t < b′, (ā, t′) ∈ r_α^{D̂_{i−1}} with
t = t′ + (τᵢ − τ_{i−1})}`. -/
def sinceStep (τ : ℕ → ℕ) (I : Interval) (i : ℕ) (B G rprev : Set (List ℕ)) : Set (List ℕ) :=
  {x | ∃ a : List ℕ, a ∈ G ∧ x = a ++ [0]} ∪
    (if i = 0 then ∅ else
      {x | ∃ (a : List ℕ) (t t' : ℕ), x = a ++ [t] ∧ a ∈ B ∧ (t : ℕ∞) < I.hi ∧ a ++ [t'] ∈ rprev ∧
        t = t' + (τ i - τ (i - 1))})

/-- `r_α^{D̂ᵢ}` for `α = β S_I γ`, by recursion on `i`, from the families `B j = β̂^{D̂ⱼ}` and
`G j = γ̂^{D̂ⱼ}`. -/
def sinceR (τ : ℕ → ℕ) (I : Interval) (B G : ℕ → Set (List ℕ)) : ℕ → Set (List ℕ)
  | 0 => sinceStep τ I 0 (B 0) (G 0) ∅
  | i + 1 => sinceStep τ I (i + 1) (B (i + 1)) (G (i + 1)) (sinceR τ I B G i)

/-- `p_α^{D̂ᵢ} = {ā | (ā, t) ∈ r_α^{D̂ᵢ} for some t ≥ b}` for `α = β S_{[b,b′)} γ`. -/
def sinceP (I : Interval) (r : Set (List ℕ)) : Set (List ℕ) :=
  {a | ∃ t : ℕ, I.lo ≤ t ∧ a ++ [t] ∈ r}

/-! ### §3.4.4: until with `b′ ∈ ℕ` (pp. 15:12–15:13), with repairs R1–R3. -/

/-- Since `τ̄` is monotone and makes progress, for every `b′` and `i` some `m` has
`τ_{i+m} − τᵢ ≥ b′`. -/
theorem TempStruct.exists_lookahead (D : TempStruct S) (b' i : ℕ) :
    ∃ m, b' ≤ D.τ (i + m) - D.τ i := by
  obtain ⟨m, hm⟩ := D.progress (D.τ i + b')
  refine ⟨m - i, ?_⟩
  rcases le_or_gt i m with h | h
  · rw [Nat.add_sub_cancel' h]; omega
  · have := D.mono h.le; omega

/-- The lookahead offset `ℓᵢ = max{j ∈ ℕ | τ_{i+j} − τᵢ < b′}` (p. 15:12): the least `m` with
`τ_{i+m} − τᵢ ≥ b′`, minus one. (For `b′ > 0` that least `m` is at least `1`.) -/
def lookahead (D : TempStruct S) (b' i : ℕ) : ℕ := Nat.find (D.exists_lookahead b' i) - 1

/-- `ℓ_{i−1}`, with the convention `ℓ_{−1} := 0` (p. 15:13). -/
def prevLookahead (D : TempStruct S) (b' i : ℕ) : ℕ := if i = 0 then 0 else lookahead D b' (i - 1)

/-- One step of the until construction for `α = β U_{[b,b′)} γ`, `b′ = I.hi` finite, at time point
`i`, from the families `B m = β̂^{D̂ₘ}`, `G m = γ̂^{D̂ₘ}` (read only at the points
`i + ℓ_{i−1}, …, i + ℓᵢ`) and `rprev = r_α^{D̂_{i−1}}`, `sprev = s_α^{D̂_{i−1}}`. Returns
`(r_α^{D̂ᵢ}, s_α^{D̂ᵢ}) = (N_r ∪ U_r, N_s ∪ U_s ∪ E_s)`. A pair `(ā, j)` is `ā ++ [j]`, a quadruple
`(ā, j, j′, t)` is `ā ++ [j, j′, t]`; `j - 1` is the page's `j ⊖ 1`.

Repairs of the printed construction: (R1) the guard of `U_r` is "`ā ∈ β̂^{D̂_{i+k}}` for all
`ℓ_{i−1} ≤ k ≤ ℓᵢ`" instead of "`(ā, ℓ_{i−1}) ∈ N_r`"; (R2) `U_s` keeps only tuples with `j′ ≥ 1`;
(R3) `t = t′ − (τᵢ − τ_{i−1})` is the equation `t + (τᵢ − τ_{i−1}) = t′`. -/
def untilStep (D : TempStruct S) (I : Interval) (i : ℕ) (B G : ℕ → Set (List ℕ))
    (rprev sprev : Set (List ℕ)) : Set (List ℕ) × Set (List ℕ) :=
  let b := I.lo
  let ℓ := lookahead D I.hi.toNat i
  let ℓp := prevLookahead D I.hi.toNat i
  let Nr : Set (List ℕ) :=
    {x | ∃ (a : List ℕ) (j : ℕ), x = a ++ [j] ∧ ℓp ≤ j ∧ j ≤ ℓ ∧ ∀ k, j ≤ k → k ≤ ℓ → a ∈ B (i + k)}
  let Ur : Set (List ℕ) := if i = 0 then ∅ else
    {x | ∃ (a : List ℕ) (j : ℕ), x = a ++ [j - 1] ∧ a ++ [j] ∈ rprev ∧ ∀ k, ℓp ≤ k → k ≤ ℓ → a ∈ B (i + k)}
  let Ns : Set (List ℕ) :=
    {x | ∃ (a : List ℕ) (j j' t : ℕ), x = a ++ [j, j', t] ∧ ℓp ≤ j ∧ j ≤ j' ∧ j' ≤ ℓ ∧ a ∈ G (i + j') ∧
      t = D.τ (i + j') - D.τ i ∧ b ≤ t ∧ ∀ k, j ≤ k → k < j' → a ∈ B (i + k)}
  let Us : Set (List ℕ) := if i = 0 then ∅ else
    {x | ∃ (a : List ℕ) (j j' t t' : ℕ), x = a ++ [j - 1, j' - 1, t] ∧ a ++ [j, j', t'] ∈ sprev ∧ 1 ≤ j' ∧
      t + (D.τ i - D.τ (i - 1)) = t' ∧ b ≤ t}
  let Es : Set (List ℕ) := if i = 0 then ∅ else
    {x | ∃ (a : List ℕ) (j j' t : ℕ), x = a ++ [j - 1, j', t] ∧ a ++ [j] ∈ rprev ∧ a ++ [ℓp, j', t] ∈ Ns}
  (Nr ∪ Ur, Ns ∪ Us ∪ Es)

/-- `(r_α^{D̂ᵢ}, s_α^{D̂ᵢ})` for `α = β U_I γ`, by recursion on `i`. -/
def untilRS (D : TempStruct S) (I : Interval) (B G : ℕ → Set (List ℕ)) :
    ℕ → Set (List ℕ) × Set (List ℕ)
  | 0 => untilStep D I 0 B G ∅ ∅
  | i + 1 => untilStep D I (i + 1) B G (untilRS D I B G i).1 (untilRS D I B G i).2

/-- `p_α^{D̂ᵢ} = {ā | (ā, 0, j′, t) ∈ s_α^{D̂ᵢ} for some j′, t ≥ 0}` for `α = β U_I γ`. -/
def untilP (s : Set (List ℕ)) : Set (List ℕ) :=
  {a | ∃ j' t : ℕ, a ++ [0, j', t] ∈ s}

end MFOTLMon.Monitor


