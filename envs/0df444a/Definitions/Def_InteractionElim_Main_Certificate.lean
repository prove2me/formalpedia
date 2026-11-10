-- Prove2me | Definitions.Def_InteractionElim_Main_Certificate
-- name    : InteractionElim_Main_Certificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:19:42.710194+00:00
-- url     : https://prove2.me/theorems/d1252441-2ede-40fe-85a8-bcd0b61193a0
-- title:
--   Binary orthogonal complements, the fractional distinguishing certificate $\tau(z,C)$, saturated cells, and the objectives $F(W)$, $G(W)$
-- statement:
--   All vector spaces are over $\mathbb F_2$. For a finite index set $\iota$ (for $\mathbb F_2^r$ take $\iota=\{1,\dots,r\}$) and a subspace $W\le\mathbb F_2^\iota$, the **orthogonal complement** for the standard binary dot product is $W^\perp=\{v: v\cdot w=0\ \text{for all } w\in W\}$.
--
--   For a set $C\subseteq\mathbb F_2^\iota$ and a root $z$, a **feasible certificate** is a weight vector $a\in\mathbb R^\iota$ with $a_i\ge 0$ and $\sum_{i:\,z_i\ne y_i}a_i\ge 1$ for every $y\in C\setminus\{z\}$. The **fractional distinguishing certificate** (Eq. (2.4)) is
--   $$
--   \tau(z,C)=\inf\Big\{\sum_{i}a_i:\ a \text{ feasible}\Big\};
--   $$
--   it is $0$ for a singleton $C=\{z\}$.
--
--   A set $C$ is **saturated** under a subspace $K$ if $C+K=C$. With $r=|\iota|$, the objectives (2.5)–(2.6) are
--   $$
--   F(W)=\min_{\substack{C\ne\emptyset\\ C+W^\perp=C}}\Big\{r-\log_2|C|+\frac1{|C|}\sum_{z\in C}\tau(z,C)\Big\},\qquad
--   G(W)=\min_{V\le W}\big\{\dim V+\tau(0,V^\perp)\big\}.
--   $$
--   Finally $H_2(p)=-\sum_z p(z)\log_2 p(z)$ is the base-two entropy of a distribution $p$ on $\mathbb F_2^\iota$ (with $0\log 0=0$).
--
--   $F$ prices a lesson that may teach any union of knowledge fibers (saturated cells): description deficit plus the average certificate the agent must still verify. $G$ prices linear lessons, whose cells are cosets.
--
--   **Formalization Note** `tau z C` is `sInf` of the set of masses of feasible certificates; that set is nonempty (all-ones weights are feasible) and bounded below by $0$, so `sInf` is the infimum (the LP minimum) and the definition does not presuppose attainment. `Saturated C K` is written as $c+v\in C$ for $c\in C$, $v\in K$, which is $C+K=C$ because $0\in K$. `F` and `G` are `sInf` of the image of a finite nonempty family (the whole space is a saturated cell; $V=0$ is a subspace of $W$), bounded below by $0$, so they are minima. $\log_2$ is `Real.logb 2`.
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), pp. 3-5, §2 notation and Eqs. (2.4)-(2.6)

import Mathlib

open scoped BigOperators

namespace InteractionElim.Main

/-!
# Binary orthogonal complements, the fractional distinguishing certificate, and `F`, `G`

Source: Jin, Zang, Xu, Li, *Eliminating Ongoing Interaction in Long-Running Verification Agents*,
STOC 2027 submission (manuscript sha256 44f6d829…), §2, p. 3–5, Eqs. (2.4)–(2.6).

Vectors of `F_2^ι` are functions `ι → ZMod 2` over a finite index type `ι`; for `F_2^r` take
`ι = Fin r`. All spaces are over `F_2` and orthogonality is the standard binary dot product.
-/

/-- The orthogonal complement `W^⊥ = {v : v · w = 0 for all w ∈ W}` for the standard binary dot
product. -/
def orth {ι : Type*} [Fintype ι] (W : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {v | ∀ w ∈ W, v ⬝ᵥ w = 0}
  add_mem' := by
    intro a b ha hb w hw
    simp [add_dotProduct, ha w hw, hb w hw]
  zero_mem' := by
    intro w _
    simp
  smul_mem' := by
    intro c a ha w hw
    simp [smul_dotProduct, ha w hw]

/-- `a` is a feasible fractional distinguishing certificate for the root `z` against the set `C`
(Eq. (2.4)): `a_i ≥ 0` and `∑_{i : z_i ≠ y_i} a_i ≥ 1` for every `y ∈ C \ {z}`. -/
def IsCertificate {ι : Type*} [Fintype ι] (C : Set (ι → ZMod 2)) (z : ι → ZMod 2)
    (a : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧
    ∀ y ∈ C, y ≠ z → 1 ≤ ∑ i ∈ Finset.univ.filter (fun i => z i ≠ y i), a i

/-- The fractional distinguishing certificate `τ(z, C)` of Eq. (2.4): the infimum of the total
mass `∑_i a_i` over feasible certificates. The feasible set is nonempty (all-ones weights) and
the masses are nonnegative, so this is a genuine infimum of a nonempty set bounded below; for a
singleton `C = {z}` it is `0`. -/
noncomputable def tau {ι : Type*} [Fintype ι] (z : ι → ZMod 2) (C : Set (ι → ZMod 2)) : ℝ :=
  sInf {t : ℝ | ∃ a : ι → ℝ, IsCertificate C z a ∧ t = ∑ i, a i}

/-- `C` is saturated under the subspace `K`: `C + K = C`, i.e. `c + v ∈ C` for all `c ∈ C`,
`v ∈ K` (the reverse inclusion holds because `0 ∈ K`). -/
def Saturated {ι : Type*} (C : Set (ι → ZMod 2)) (K : Submodule (ZMod 2) (ι → ZMod 2)) : Prop :=
  ∀ c ∈ C, ∀ v ∈ K, c + v ∈ C

/-- The objective of a cell in Eq. (2.5): description deficit plus average root certificate,
`r − log₂|C| + |C|⁻¹ ∑_{z ∈ C} τ(z, C)` with `r = |ι|`. -/
noncomputable def cellObjective {ι : Type*} [Fintype ι] (C : Finset (ι → ZMod 2)) : ℝ :=
  (Fintype.card ι : ℝ) - Real.logb 2 C.card + (1 / (C.card : ℝ)) * ∑ z ∈ C, tau z (C : Set _)

/-- `F(W)` of Eq. (2.5): the minimum of `cellObjective C` over nonempty cells `C ⊆ F_2^ι` with
`C + W^⊥ = C`. The family is finite and nonempty (it contains the whole space), so the
infimum is a minimum. -/
noncomputable def F {ι : Type*} [Fintype ι] (W : Submodule (ZMod 2) (ι → ZMod 2)) : ℝ :=
  sInf (cellObjective '' {C : Finset (ι → ZMod 2) | C.Nonempty ∧ Saturated (C : Set _) (orth W)})

/-- `G(W)` of Eq. (2.6): the minimum over subspaces `V ≤ W` of `dim V + τ(0, V^⊥)`. The family
is finite and nonempty (`V = 0`), so the infimum is a minimum. -/
noncomputable def G {ι : Type*} [Fintype ι] (W : Submodule (ZMod 2) (ι → ZMod 2)) : ℝ :=
  sInf ((fun V : Submodule (ZMod 2) (ι → ZMod 2) =>
      (Module.finrank (ZMod 2) V : ℝ) + tau 0 (orth V : Set (ι → ZMod 2))) ''
    {V | V ≤ W})

/-- Base-two Shannon entropy `H₂(p) = −∑_z p(z) log₂ p(z)` of a function `p` on `F_2^ι`
(used for probability distributions; the term with `p(z) = 0` is `0`). -/
noncomputable def entropy2 {ι : Type*} [Fintype ι] [DecidableEq ι] (p : (ι → ZMod 2) → ℝ) : ℝ :=
  -∑ z, p z * Real.logb 2 (p z)

end InteractionElim.Main


