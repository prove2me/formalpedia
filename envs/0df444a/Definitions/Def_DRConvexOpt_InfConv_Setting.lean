-- Prove2me | Definitions.Def_DRConvexOpt_InfConv_Setting
-- name    : DRConvexOpt_InfConv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:00.402547+00:00
-- url     : https://prove2.me/theorems/b8bc95f3-f219-4bd2-8b16-2d6fb4957d09
-- title:
--   (3)–(5), (C3), (N′), 𝒫^j, (6), (7), Γ(x), pp. 3, 7–12 — ambiguity set, outer approximations, naïve and infimal convolution bounds
-- statement:
--   This module fixes the objects of §2 and §2.2 of Wiesemann, Kuhn and Sim, *Distributionally Robust Convex Optimization*.
--
--   Throughout, $z \in \mathbb R^P$ and $u \in \mathbb R^Q$, and the joint outcome space is $\mathbb R^P \times \mathbb R^Q$ with its Borel $\sigma$-algebra.
--
--   1. A **proper cone** $\mathcal K \subseteq \mathbb R^m$ (Notation, p. 7) is a closed convex cone that is pointed, $\mathcal K \cap (-\mathcal K) = \{0\}$, and has nonempty interior; $x \preccurlyeq_{\mathcal K} y$ means $y - x \in \mathcal K$. Its **dual cone** is $\mathcal K^\star = \{y : x^\top y \ge 0 \text{ for all } x \in \mathcal K\}$. A set $A$ is **strictly included** in $B$, $A \Subset B$, if $A$ lies in the interior of $B$.
--   2. The **confidence sets** are $\mathcal C_i = \{(z,u) : C_i z + D_i u \preccurlyeq_{\mathcal K_i} c_i\}$, $i \in \mathcal I = \{1,\dots,I\}$, and the **standardized ambiguity set** (4) is
--   $$\mathcal P = \Big\{\mathbb P \in \mathcal P_0(\mathbb R^P\times\mathbb R^Q) : \mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b,\ \ \mathbb P[(\tilde z,\tilde u) \in \mathcal C_i] \in [\underline p_i, \overline p_i]\ \forall i \in \mathcal I\Big\}.$$
--   3. The constraint function (C3) is $v(x,z) = \max_{l \in \mathcal L}\, (S_l z + s_l)^\top x + \mathbf t_l^\top z + t_l$, $L \ge 1$ pieces, with $\mathbf t_l$ a vector and $t_l$ a scalar.
--   4. A **partition** $\{\mathcal I_j\}_{j \in \mathcal J}$ of $\mathcal I$ satisfies the **weak nesting condition** (N′) if for every $j$ and all $i \ne i'$ in $\mathcal I_j$, either $\mathcal C_i \Subset \mathcal C_{i'}$, $\mathcal C_{i'} \Subset \mathcal C_i$ or $\mathcal C_i \cap \mathcal C_{i'} = \emptyset$.
--   5. The **outer approximations** (p. 12) keep only the probability conditions of one block:
--   $$\mathcal P^j = \Big\{\mathbb P \in \mathcal P_0(\mathbb R^P\times\mathbb R^Q) : \mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b,\ \ \mathbb P[(\tilde z,\tilde u) \in \mathcal C_i] \in [\underline p_i, \overline p_i]\ \forall i \in \mathcal I_j\Big\},\qquad j \in \mathcal J.$$
--   6. For a set of distributions $\mathcal Q$, the **worst-case expectation** $\sup_{\mathbb P \in \mathcal Q} \mathbb E_{\mathbb P}[\varphi]$ is an extended real: $-\infty$ for empty $\mathcal Q$, $+\infty$ when unbounded.
--   7. The feasible set $\Gamma(x) = \{(y,\delta) : y_j \in \mathbb R^N,\ \delta_j \in \mathbb R,\ \sum_j y_j = x,\ \sum_j \delta_j = 1,\ \delta > 0\}$.
--   8. The left-hand side of the **naïve approximation** (6) is $\min_{j \in \mathcal J} \sup_{\mathbb P \in \mathcal P^j} \mathbb E_{\mathbb P}[v(x,\tilde z)]$, and that of the **infimal convolution bound** (7) is
--   $$\inf_{(y,\delta) \in \Gamma(x)} \sum_{j \in \mathcal J} \delta_j \sup_{\mathbb P \in \mathcal P^j} \mathbb E_{\mathbb P}[v(y_j/\delta_j, \tilde z)].$$
--   9. A condition **not in the paper**, recorded for use as an explicit hypothesis: the **uniform first-moment bound**, for every $j$ there is $M_j$ with $\mathbb E_{\mathbb P}\|\tilde z\| \le M_j$ for all $\mathbb P \in \mathcal P^j$.
--
--   These are the objects in which Theorem 3, the steps of its proof, and Proposition 1 are stated.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` with the sup norm; $Mx$ is `M *ᵥ x`, $x^\top y$ is `x ⬝ᵥ y`. The index set $\mathcal I$ is `Fin (nI + 1)` (0-based, so $I \ge 1$) and $\mathcal C_I$ is index `Fin.last nI`. The partition is a block map `blk : Fin (nI + 1) → Fin nJ` with $\mathcal I_j = \{i : \mathrm{blk}\, i = j\}$; the theorems require it surjective, so that every block is nonempty. Members of $\mathcal P$ and of every $\mathcal P^j$ carry the clause `Integrable (fun ω => ω) μ` (finite first moment), because a Lean integral of a non-integrable map is $0$. The bounds (6) and (7) take values in `EReal`; the minimum over the finite $\mathcal J$ is an infimum, and $y_j/\delta_j$ is `(δ j)⁻¹ • y j`, used only on $\Gamma(x)$ where $\delta > 0$. The shared objects (cones, confidence sets, $\mathcal P$, $v$, $\Subset$) are copied word for word from the other missions of this series.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 3, 7–12: (3), Notation (p. 7), (4), (5), (C3), (N′), 𝒫^j, (6), (7), Γ(x)

import Mathlib

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix

/-- Notation, p. 7: `K` is a proper cone — a closed convex cone that is pointed (salient:
`K ∩ −K = {0}`) and has nonempty interior. -/
def IsProperCone {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  IsClosed K ∧ (0 : Fin m → ℝ) ∈ K ∧ (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧
    (∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K) ∧ (∀ x ∈ K, -x ∈ K → x = 0) ∧ (interior K).Nonempty

/-- Notation, p. 7: the dual cone `K⋆ = {y : xᵀy ≥ 0 for all x ∈ K}`. -/
def dualCone {m : ℕ} (K : Set (Fin m → ℝ)) : Set (Fin m → ℝ) := {y | ∀ x ∈ K, 0 ≤ x ⬝ᵥ y}

/-- The confidence set (5), p. 8: `{(z, u) : C z + D u ≼_K c}`, i.e. `c − (C z + D u) ∈ K`. -/
def confSet {nP nQ m : ℕ} (C : Matrix (Fin m) (Fin nP) ℝ) (D : Matrix (Fin m) (Fin nQ) ℝ)
    (c : Fin m → ℝ) (K : Set (Fin m → ℝ)) : Set ((Fin nP → ℝ) × (Fin nQ → ℝ)) :=
  {ω | c - (C *ᵥ ω.1 + D *ᵥ ω.2) ∈ K}

/-- The data of the standardized ambiguity set (4)–(5), p. 8. The index set `𝓘 = {1, …, I}` is
`Fin (nI + 1)` (0-based), so that `I ≥ 1`; the paper's `C_I` is the index `Fin.last nI`.
`L i` is the dimension `L_i` of the cone `K_i`; `plo i`, `phi i` are `p̲_i`, `p̄_i`. -/
structure AmbData (nP nQ nK nI : ℕ) where
  /-- `A ∈ ℝ^{K×P}` -/
  A : Matrix (Fin nK) (Fin nP) ℝ
  /-- `B ∈ ℝ^{K×Q}` -/
  B : Matrix (Fin nK) (Fin nQ) ℝ
  /-- `b ∈ ℝ^K` -/
  b : Fin nK → ℝ
  /-- the cone dimensions `L_i` -/
  L : Fin (nI + 1) → ℕ
  /-- `C_i ∈ ℝ^{L_i×P}` -/
  C : (i : Fin (nI + 1)) → Matrix (Fin (L i)) (Fin nP) ℝ
  /-- `D_i ∈ ℝ^{L_i×Q}` -/
  D : (i : Fin (nI + 1)) → Matrix (Fin (L i)) (Fin nQ) ℝ
  /-- `c_i ∈ ℝ^{L_i}` -/
  c : (i : Fin (nI + 1)) → Fin (L i) → ℝ
  /-- the cones `K_i` -/
  K : (i : Fin (nI + 1)) → Set (Fin (L i) → ℝ)
  /-- the lower probability bounds `p̲_i` -/
  plo : Fin (nI + 1) → ℝ
  /-- the upper probability bounds `p̄_i` -/
  phi : Fin (nI + 1) → ℝ

/-- The confidence set `C_i` of (5). -/
def AmbData.conf {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) (i : Fin (nI + 1)) :
    Set ((Fin nP → ℝ) × (Fin nQ → ℝ)) :=
  confSet (d.C i) (d.D i) (d.c i) (d.K i)

/-- The standardized ambiguity set (4), p. 8: the probability distributions `ℙ` of `(z̃, ũ)` with
finite first moment such that `E_ℙ[A z̃ + B ũ] = b` and `ℙ[(z̃, ũ) ∈ C_i] ∈ [p̲_i, p̄_i]` for all
`i`. -/
def ambiguitySet {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) :
    Set (Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) :=
  {μ | IsProbabilityMeasure μ ∧ Integrable (fun ω => ω) μ ∧
       ∫ ω, (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ∂μ = d.b ∧
       ∀ i, μ.real (d.conf i) ∈ Set.Icc (d.plo i) (d.phi i)}

/-- The data of a constraint function satisfying (C3), p. 9:
`v(x, z) = max_{l ∈ ℒ} (S_l z + s_l)ᵀ x + t_lᵀ z + t_l`, where `tv l` is the vector `t_l ∈ ℝ^P`
and `t0 l` is the scalar `t_l ∈ ℝ`. -/
structure PWAff (nN nP nL : ℕ) where
  /-- `S_l ∈ ℝ^{N×P}` -/
  S : Fin nL → Matrix (Fin nN) (Fin nP) ℝ
  /-- `s_l ∈ ℝ^N` -/
  s : Fin nL → Fin nN → ℝ
  /-- the vector `t_l ∈ ℝ^P` (bold in the paper) -/
  tv : Fin nL → Fin nP → ℝ
  /-- the scalar `t_l ∈ ℝ` -/
  t0 : Fin nL → ℝ

/-- The constraint function `v(x, z) = max_l v_l(x, z)` of (C3), with
`v_l(x, z) = (S_l z + s_l)ᵀ x + t_lᵀ z + t_l`. -/
def PWAff.eval {nN nP nL : ℕ} [NeZero nL] (v : PWAff nN nP nL) (x : Fin nN → ℝ)
    (z : Fin nP → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    (v.S l *ᵥ z + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ z + v.t0 l)

/-- Strict inclusion, Notation p. 7: `S ⋐ T` iff `S` is contained in the interior of `T`. -/
def SInc {α : Type*} [TopologicalSpace α] (S T : Set α) : Prop := S ⊆ interior T

/-- The weak nesting condition (N′), pp. 11–12, for the partition `{𝓘_j}_{j ∈ 𝒥}` given by the
block map `blk` (`𝓘_j = {i : blk i = j}`): for all `j` and all `i ≠ i'` in `𝓘_j`, either
`C_i ⋐ C_{i'}`, `C_{i'} ⋐ C_i` or `C_i ∩ C_{i'} = ∅`. -/
def WeakNesting {nP nQ nK nI nJ : ℕ} (d : AmbData nP nQ nK nI)
    (blk : Fin (nI + 1) → Fin nJ) : Prop :=
  ∀ i i', i ≠ i' → blk i = blk i' →
    SInc (d.conf i) (d.conf i') ∨ SInc (d.conf i') (d.conf i) ∨ Disjoint (d.conf i) (d.conf i')

/-- The outer approximation `𝒫^j` of the ambiguity set, p. 12: the probability distributions with
finite first moment such that `E_ℙ[A z̃ + B ũ] = b` and `ℙ[(z̃, ũ) ∈ C_i] ∈ [p̲_i, p̄_i]` for all
`i ∈ 𝓘_j`, i.e. all `i` with `blk i = j`. -/
def outerSet {nP nQ nK nI nJ : ℕ} (d : AmbData nP nQ nK nI)
    (blk : Fin (nI + 1) → Fin nJ) (j : Fin nJ) :
    Set (Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) :=
  {μ | IsProbabilityMeasure μ ∧ Integrable (fun ω => ω) μ ∧
       ∫ ω, (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ∂μ = d.b ∧
       ∀ i, blk i = j → μ.real (d.conf i) ∈ Set.Icc (d.plo i) (d.phi i)}

/-- The worst-case expectation `sup_{ℙ ∈ 𝒫} E_ℙ[φ]` as an extended real: `⊥` (= −∞) if `𝒫` is empty
and `⊤` (= +∞) if the expectations are unbounded above. -/
noncomputable def worstCase {Ω : Type*} [MeasurableSpace Ω] (P : Set (Measure Ω)) (φ : Ω → ℝ) :
    EReal :=
  ⨆ μ ∈ P, ((∫ ω, φ ω ∂μ : ℝ) : EReal)

/-- The feasible set `Γ(x)` of p. 12: pairs `(y, δ)` with `y = (y_j)_{j ∈ 𝒥}`, `y_j ∈ ℝ^N`,
`δ = (δ_j)_{j ∈ 𝒥}`, `∑_j y_j = x`, `∑_j δ_j = 1` and `δ > 0` (every `δ_j > 0`). -/
def Gamma {nJ nN : ℕ} (x : Fin nN → ℝ) : Set ((Fin nJ → Fin nN → ℝ) × (Fin nJ → ℝ)) :=
  {p | (∑ j, p.1 j) = x ∧ (∑ j, p.2 j) = 1 ∧ ∀ j, 0 < p.2 j}

/-- The left-hand side of the naïve approximation (6), p. 12:
`min_{j ∈ 𝒥} sup_{ℙ ∈ 𝒫^j} E_ℙ[v(x, z̃)]` (a minimum over the finite set `𝒥`). -/
noncomputable def naiveBound {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (blk : Fin (nI + 1) → Fin nJ) (v : PWAff nN nP nL)
    (x : Fin nN → ℝ) : EReal :=
  ⨅ j, worstCase (outerSet d blk j) (fun ω => v.eval x ω.1)

/-- The left-hand side of the infimal convolution bound (7), p. 12:
`inf_{(y, δ) ∈ Γ(x)} ∑_{j ∈ 𝒥} δ_j sup_{ℙ ∈ 𝒫^j} E_ℙ[v(y_j / δ_j, z̃)]`. -/
noncomputable def infConvBound {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (blk : Fin (nI + 1) → Fin nJ) (v : PWAff nN nP nL)
    (x : Fin nN → ℝ) : EReal :=
  ⨅ p ∈ Gamma x, ∑ j, ((p.2 j : ℝ) : EReal) *
    worstCase (outerSet d blk j) (fun ω => v.eval ((p.2 j)⁻¹ • p.1 j) ω.1)

/-- An assumption added to the paper's (disclosed): the first moments of `z̃` are bounded uniformly
over each outer approximation `𝒫^j`. It supplies the claim "sup_{ℙ ∈ 𝒫^j} E_ℙ[v(0, z̃)] is finite
for all j ∈ 𝒥" used without proof on p. 37. -/
def UnifFirstMoment {nP nQ nK nI nJ : ℕ} (d : AmbData nP nQ nK nI)
    (blk : Fin (nI + 1) → Fin nJ) : Prop :=
  ∀ j, ∃ M : ℝ, ∀ μ ∈ outerSet d blk j, ∫ ω, ‖ω.1‖ ∂μ ≤ M

end DRConvexOpt.InfConv


