-- Prove2me | Definitions.Def_DRConvexOpt_Reform_Setting
-- name    : DRConvexOpt_Reform_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:26.619413+00:00
-- url     : https://prove2.me/theorems/afece418-2c08-456f-9687-d045d4cf9717
-- title:
--   (3)–(5), (C1)–(C3), (N), Notation, pp. 3, 7–10, 35 — proper and dual cones, confidence sets, the standardized ambiguity set, piecewise-affine v, nesting, 𝒜(i), 𝒟(i), C̄_i
-- statement:
--   This module fixes the objects of §2 of Wiesemann, Kuhn and Sim, *Distributionally Robust Convex Optimization*.
--
--   Throughout, $z \in \mathbb R^P$ and $u \in \mathbb R^Q$, and the joint outcome space is $\mathbb R^P \times \mathbb R^Q$ with its Borel $\sigma$-algebra.
--
--   1. A **proper cone** $\mathcal K \subseteq \mathbb R^m$ (Notation, p. 7) is a closed convex cone that is pointed, $\mathcal K \cap (-\mathcal K) = \{0\}$, and has nonempty interior; $x \preccurlyeq_{\mathcal K} y$ means $y - x \in \mathcal K$. Its **dual cone** is $\mathcal K^\star = \{y : x^\top y \ge 0 \text{ for all } x \in \mathcal K\}$.
--   2. A set $A$ is **strictly included** in $B$, written $A \Subset B$, if $A$ is contained in the interior of $B$.
--   3. The data of the **standardized ambiguity set** (4)–(5) are $A \in \mathbb R^{K\times P}$, $B \in \mathbb R^{K \times Q}$, $b \in \mathbb R^K$, and for each $i \in \mathcal I = \{1,\dots,I\}$ matrices $C_i \in \mathbb R^{L_i \times P}$, $D_i \in \mathbb R^{L_i\times Q}$, a vector $c_i \in \mathbb R^{L_i}$, a cone $\mathcal K_i \subseteq \mathbb R^{L_i}$ and probability bounds $\underline p_i, \overline p_i$. The **confidence sets** are
--   $$\mathcal C_i = \{(z,u) \in \mathbb R^P \times \mathbb R^Q : C_i z + D_i u \preccurlyeq_{\mathcal K_i} c_i\}.$$
--   4. The **ambiguity set** is
--   $$\mathcal P = \Big\{\mathbb P \in \mathcal P_0(\mathbb R^P\times\mathbb R^Q) : \mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b,\ \ \mathbb P[(\tilde z,\tilde u) \in \mathcal C_i] \in [\underline p_i, \overline p_i]\ \forall i \in \mathcal I\Big\},$$
--   where every member is required to have a finite first moment, so that the expectation exists.
--   5. A **constraint function satisfying (C3)** is $v(x,z) = \max_{l \in \mathcal L} v_l(x,z)$, $\mathcal L = \{1,\dots,L\}$, $L \ge 1$, with
--   $$v_l(x,z) = (S_l z + s_l)^\top x + \mathbf t_l^\top z + t_l,$$
--   where $S_l \in \mathbb R^{N\times P}$, $s_l \in \mathbb R^N$, $\mathbf t_l \in \mathbb R^P$ is a vector and $t_l \in \mathbb R$ a scalar.
--   6. The **nesting condition** (N), p. 10: for all $i \neq i'$, either $\mathcal C_i \Subset \mathcal C_{i'}$, $\mathcal C_{i'} \Subset \mathcal C_i$, or $\mathcal C_i \cap \mathcal C_{i'} = \emptyset$. The **antecedents** and **descendants** of $\mathcal C_i$ are $\mathcal A(i) = \{i\} \cup \{i' : \mathcal C_i \Subset \mathcal C_{i'}\}$ and $\mathcal D(i) = \{i' : \mathcal C_{i'} \Subset \mathcal C_i\}$, and $\overline{\mathcal C}_i = \mathcal C_i \setminus \bigcup_{i' \in \mathcal D(i)} \mathcal C_{i'}$ (proof of Theorem 1, p. 35).
--   7. Two regularity conditions that are **not in the paper** are recorded for use as explicit hypotheses: **(S1)** there is $\varepsilon > 0$ such that for every $b'$ with $\|b' - b\|_\infty \le \varepsilon$ and every $\Delta \in \mathbb R^I$ with $\|\Delta\|_\infty \le \varepsilon$ some finite nonnegative measure $\mu$ concentrated on $\mathcal C_I$, with finite first moment, satisfies $\int (Az + Bu)\,d\mu = b'$ and $\mu(\mathcal C_i) \in [\underline p_i + \Delta_i, \overline p_i + \Delta_i]$ for all $i$; **(S2)** every confidence set is strictly feasible: for each $i$ some $(z,u)$ has $c_i - C_i z - D_i u$ in the interior of $\mathcal K_i$.
--
--   These are the objects in which Theorem 1, Lemma 1 and the steps of the proof of Theorem 1 are stated.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; $Mx$ is `M *ᵥ x`, $M^\top y$ is `Mᵀ *ᵥ y`, $x^\top y$ is `x ⬝ᵥ y`. The index set $\mathcal I$ is `Fin (nI + 1)` (0-based, so $I \ge 1$), and $\mathcal C_I$ is the index `Fin.last nI`. The scalar $t_l$ is `t0 l` and the vector $\mathbf t_l$ is `tv l`. $\mathbb P[\cdot]$ is `μ.real`. Members of $\mathcal P$ carry the clause `Integrable (fun ω => ω) μ` (a finite first moment), because a Lean integral of a non-integrable map is $0$. $K = 0$ or $Q = 0$ are allowed, as on p. 8. $\mathcal D(i)$ is copied as printed, without $i' \neq i$; $\mathcal A(i)$ contains $i$ by definition.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 3, 7–10, 35: (3), Notation (p. 7), (4), (5), (C1)–(C3), (N), 𝒜(i), 𝒟(i), and C̄_i in the proof of Theorem 1

import Mathlib

namespace DRConvexOpt.Reform

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

/-- The nesting condition (N), p. 10: for all `i ≠ i'`, either `C_i ⋐ C_{i'}`, `C_{i'} ⋐ C_i` or
`C_i ∩ C_{i'} = ∅`. -/
def Nesting {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) : Prop :=
  ∀ i i', i ≠ i' → SInc (d.conf i) (d.conf i') ∨ SInc (d.conf i') (d.conf i) ∨
    Disjoint (d.conf i) (d.conf i')

open Classical in
/-- `𝒜(i) = {i} ∪ {i' ∈ 𝓘 : C_i ⋐ C_{i'}}`, p. 10 (the antecedents of `C_i`). -/
noncomputable def anc {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) (i : Fin (nI + 1)) :
    Finset (Fin (nI + 1)) :=
  insert i (Finset.univ.filter fun i' => SInc (d.conf i) (d.conf i'))

open Classical in
/-- `𝒟(i) = {i' ∈ 𝓘 : C_{i'} ⋐ C_i}`, p. 10 (the descendants of `C_i`), as printed. -/
noncomputable def desc {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) (i : Fin (nI + 1)) :
    Finset (Fin (nI + 1)) :=
  Finset.univ.filter fun i' => SInc (d.conf i') (d.conf i)

/-- `C̄_i = C_i \ ⋃_{i' ∈ 𝒟(i)} C_{i'}`, proof of Theorem 1, p. 35. -/
def cbar {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) (i : Fin (nI + 1)) :
    Set ((Fin nP → ℝ) × (Fin nQ → ℝ)) :=
  d.conf i \ ⋃ i' ∈ desc d i, d.conf i'

/-- (S1), an assumption added to the paper's: the moment problem of the proof of Theorem 1
(p. 35) stays feasible under every small common shift of `b` and of each probability interval:
there is `ε > 0` such that for all `b'` with `|b' − b| ≤ ε` (componentwise) and all `Δ` with
`|Δ_i| ≤ ε`, some finite nonnegative measure supported on `C_I`, with finite first moment, has
`∫ (A z + B u) dμ = b'` and `μ(C_i) ∈ [p̲_i + Δ_i, p̄_i + Δ_i]` for all `i`. -/
def MomentSlater {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) : Prop :=
  ∃ ε > 0, ∀ b' : Fin nK → ℝ, ∀ Δ : Fin (nI + 1) → ℝ, (∀ k, |b' k - d.b k| ≤ ε) →
    (∀ i, |Δ i| ≤ ε) →
    ∃ μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ)), IsFiniteMeasure μ ∧
      μ (d.conf (Fin.last nI))ᶜ = 0 ∧ Integrable (fun ω => ω) μ ∧
      ∫ ω, (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ∂μ = b' ∧
      ∀ i, μ.real (d.conf i) ∈ Set.Icc (d.plo i + Δ i) (d.phi i + Δ i)

/-- (S2), an assumption added to the paper's: every confidence set `C_i` is strictly feasible,
i.e. some `(z, u)` has `c_i − (C_i z + D_i u)` in the interior of `K_i`. -/
def ConfSlater {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) : Prop :=
  ∀ i, ∃ ω : (Fin nP → ℝ) × (Fin nQ → ℝ), d.c i - (d.C i *ᵥ ω.1 + d.D i *ᵥ ω.2) ∈ interior (d.K i)

end DRConvexOpt.Reform


