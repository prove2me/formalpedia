-- Prove2me | Definitions.Def_GenKraus_StdForm_Setting
-- name    : GenKraus_StdForm_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:14.994261+00:00
-- url     : https://prove2.me/theorems/f3c13cd3-946c-4b2d-8917-8e9d9a9c45a6
-- title:
--   pp. 3–5, 11, 15 — trace preservation, cores, matrix normality (Def. 2), generalized standard form (Def. 1 via (19)–(20)), M (Def. 5), ℒ₊ (8), form-valued CP maps (Thm 14)
-- statement:
--   Throughout, $\mathcal H$ is a complex Hilbert space (inner product $\langle\cdot|\cdot\rangle$, conjugate-linear in the first slot), $\mathfrak T(\mathcal H)$ the trace-class operators with trace norm $\|\cdot\|_1$, and $\mathcal T^t$ a strongly continuous semigroup of trace preserving completely positive maps on $\mathfrak T(\mathcal H)$ with generator $\mathcal L$, $\mathcal L(\rho)=\lim_{t\downarrow 0}t^{-1}(\mathcal T^t(\rho)-\rho)$ in trace norm on the domain $\mathcal D(\mathcal L)$ where this limit exists.
--
--   This module fixes the objects of the paper on top of the published trace-class and semigroup layer.
--
--   1. **Dyads.** $|\varphi\rangle\langle\psi|$ is the rank-one operator $x\mapsto\langle\psi|x\rangle\,\varphi$.
--   2. **Trace preservation and strong continuity** of $\mathcal T^t$: $\operatorname{Tr}\mathcal T^t(\rho)=\operatorname{Tr}\rho$ and $\|\mathcal T^t(\rho)-\rho\|_1\to0$ as $t\downarrow0$.
--   3. **Core.** A set $S\subseteq\mathcal D(\mathcal L)$ is a core if every graph point $(\rho,\mathcal L\rho)$ is a limit, in trace norm in both components, of graph points over $S$ (closure in the graph norm $\|\rho\|_1+\|\mathcal L(\rho)\|_1$).
--   4. **Matrix normality (Definition 2).** For a basis $\{e_k\}$ let $\mathcal D_e=\operatorname{lin}\{e_k\}$ (5) and $\mathcal D_e^2=\operatorname{lin}\{|e_k\rangle\langle e_\ell|\}$ (6). The QDS is matrix normal if for some basis $\mathcal D_e^2$ is a core for $\mathcal L$.
--   5. **Generalized standard form (Definition 1).** A countable family $L_k$ and an operator $M$ on $\mathcal H$, all densely defined, with $M$ closed and $-M$ the generator of a strongly continuous semigroup on $\mathcal H$, $\mathcal D(M)\subseteq\mathcal D(L_k)$ and each $L_k$ relatively bounded with respect to $M$, such that for $\varphi,\psi\in\mathcal D(M)$
--
--   $$\mathcal L(|\varphi\rangle\langle\psi|)=\sum_k|L_k\varphi\rangle\langle L_k\psi|-|M\varphi\rangle\langle\psi|-|\varphi\rangle\langle M\psi|,\qquad \sum_k\|L_k\varphi\|^2=\langle\varphi|M\varphi\rangle+\langle M\varphi|\varphi\rangle,$$
--
--   the first sum converging in trace norm, and such that $\mathcal D_0$, the finite sums of dyads $|\varphi_n\rangle\langle\psi_n|$ with $\varphi_n,\psi_n\in\mathcal D(M)$, is a core for $\mathcal L$.
--   6. **The operator $M$ of Definition 5 and the expander (8)**, built from a unit vector $\chi\in\mathcal D_e$ (see the theorems that use them), and $\mathcal M(\rho)=M\rho+\rho M^\dagger$ (15) on dyads.
--   7. **Form-valued completely positive maps (Theorem 14).** For two orthonormal bases $\{e_n\},\{f_n\}$ indexed by $\mathbb N$, a linear map $Q$ from $\mathcal D_e^2$ to sesquilinear forms on $\mathcal D_f=\operatorname{lin}\{f_n\}$ is completely positive if $\sum_{a,c}\langle g_a|Q(\rho_{ac})|g_c\rangle\ge0$ for every positive block $(\rho_{ac})_{a,c\le n}$ of elements of $\mathcal D_e^2$ and all $g_a\in\mathcal D_f$; $E_{k\ell}=|e_k\rangle\langle e_\ell|$ are the matrix units.
--
--   These objects are shared by every statement of the mission: the goal (Theorem 3) is the equivalence of items 4 and 5.
--
--   **Formalization Note** "Basis" is an orthonormal set with dense span (Gram–Schmidt preserves finite spans, so nothing is lost). Definition 1's equations (3)–(4) with the generalized operators $L_k^\dagger, M^\dagger$ are encoded through the paper's own reformulation (19)–(20) on p. 11; (3) is required on dyads of $\mathcal D(M)$, which gives it on all of $\mathcal D_0$ by linearity of the generator. "$M$ generates a semigroup" assumes no contractivity (`HilbertC0Semigroup`, `IsMinusGenerator`: $-M$ with exactly the domain $\mathcal D(M)$ is the Hilbert-norm right derivative at $0$). The generator value used inside $M$ and $\mathcal L_+$ (`genOp`) is a chosen graph value, $0$ off the domain; every statement using it assumes the relevant dyads lie in $\mathcal D(\mathcal L)$. The index set of the $L_k$ is a countable type, finite allowed.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, pp. 3–5, 8, 11, 15–16, Definitions 1, 2, 5, 9, 13, Eqs. (5)–(8), (15)–(16), (19)–(20), (24)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09
noncomputable section
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)

namespace GenKraus.StdForm

/-! Alazzawi–Baumgartner, *Generalized Kraus Operators and Generators of Quantum Dynamical
Semigroups*, arXiv:1306.4531v4, pp. 3–5, 8, 11, 15. The trace class `TraceClass H`, the trace
norm `traceNormValue` (0 off the trace class, so it is only applied to trace-class operators and
finite sums of dyads here), the trace `operatorTrace b`, the semigroup `TraceDynamicalSemigroup b`
and its trace-norm generator graph `InTraceGeneratorGraph` are the published objects. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- The dyad |φ⟩⟨ψ| : x ↦ ⟨ψ, x⟩ φ (inner product conjugate-linear in the first slot). -/
def dyad (φ ψ : H) : H →L[ℂ] H := InnerProductSpace.rankOne ℂ φ ψ

/-- p. 3: the semigroup preserves the trace. -/
def IsTracePreserving (T : TraceDynamicalSemigroup b) : Prop :=
  ∀ t ρ, operatorTrace b (T.maps t ρ).val = operatorTrace b ρ.val

/-- p. 3: the semigroup is strongly continuous on 𝔗(ℋ) with the trace norm. -/
def IsStronglyContinuous (T : TraceDynamicalSemigroup b) : Prop :=
  ∀ ρ : TraceClass H,
    Tendsto (fun t : NNReal => traceNormValue ((T.maps t ρ).val - ρ.val)) (𝓝 0) (𝓝 0)

/-- (6): 𝒟²_e = lin{|e_k⟩⟨e_ℓ|}, for the basis vectors `v`. -/
def matrixUnits (v : Set H) : Submodule ℂ (H →L[ℂ] H) :=
  Submodule.span ℂ {A | ∃ a ∈ v, ∃ c ∈ v, A = dyad a c}

/-- p. 3: `S` is a core of the generator ℒ: `S ⊆ 𝒟(ℒ)` and every graph point (ρ, ℒρ) is a
trace-norm limit of graph points over `S` (closure in the graph norm ‖ρ‖₁ + ‖ℒ(ρ)‖₁). -/
def IsCore (T : TraceDynamicalSemigroup b) (S : Set (TraceClass H)) : Prop :=
  S ⊆ TraceGeneratorDomain T ∧
  ∀ ρ η, InTraceGeneratorGraph T ρ η → ∀ ε > 0, ∃ ρ' ∈ S, ∃ η',
    InTraceGeneratorGraph T ρ' η' ∧ traceNormValue (ρ'.val - ρ.val) < ε ∧
      traceNormValue (η'.val - η.val) < ε

/-- Definition 2, p. 4, for a given basis: `v` is an orthonormal set with dense span (a basis
{e_k}, (5)) and 𝒟²_e is a core for the generator. -/
def IsMatrixNormalWith (T : TraceDynamicalSemigroup b) (v : Set H) : Prop :=
  Orthonormal ℂ ((↑) : v → H) ∧ Dense (Submodule.span ℂ v : Set H) ∧
    IsCore T {ρ | ρ.val ∈ matrixUnits v}

/-- Definition 2, p. 4: the QDS is matrix normal. -/
def IsMatrixNormal (T : TraceDynamicalSemigroup b) : Prop :=
  ∃ v : Set H, IsMatrixNormalWith T v

/-- (16): 𝒟₀ = finite sums of dyads |φ_n⟩⟨ψ_n| with φ_n, ψ_n ∈ D. -/
def finiteDyads (D : Submodule ℂ H) : Submodule ℂ (H →L[ℂ] H) :=
  Submodule.span ℂ {A | ∃ a ∈ D, ∃ c ∈ D, A = dyad a c}

/-- `A` is relatively bounded with respect to `M` (with 𝒟(M) ⊆ 𝒟(A)):
‖A x‖ ≤ a‖x‖ + c‖M x‖ on 𝒟(M). -/
def IsRelativelyBounded (A M : H →ₗ.[ℂ] H) (h : M.domain ≤ A.domain) : Prop :=
  ∃ a c : ℝ, ∀ x : M.domain, ‖A (Submodule.inclusion h x)‖ ≤ a * ‖(x : H)‖ + c * ‖M x‖

/-- A strongly continuous semigroup of bounded operators on ℋ (no contraction assumed). -/
structure HilbertC0Semigroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  maps : NNReal → H →L[ℂ] H
  initial : maps 0 = ContinuousLinearMap.id ℂ H
  semigroup : ∀ s t, maps (s + t) = (maps s).comp (maps t)
  orbitContinuous : ∀ x, Continuous (fun t : NNReal => maps t x)

/-- `S` is e^{−tM}: −M, with exactly the domain 𝒟(M), is the Hilbert-norm right-derivative
generator of `S`. -/
def IsMinusGenerator (S : HilbertC0Semigroup H) (M : H →ₗ.[ℂ] H) : Prop :=
  ∀ x y : H, (∃ z : M.domain, (z : H) = x ∧ -M z = y) ↔
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (S.maps t.toNNReal x - x))
      (𝓝[Set.Ioi 0] 0) (𝓝 y)

/-- Definition 1, p. 3, written in the paper's equivalent form (19)–(20), p. 11: a generalized
standard form of the generator ℒ of `T`. -/
structure GenStdForm (T : TraceDynamicalSemigroup b) where
  /-- the countable (possibly finite) index set of the L_k -/
  κ : Type
  [count : Countable κ]
  M : H →ₗ.[ℂ] H
  L : κ → H →ₗ.[ℂ] H
  M_dense : Dense (M.domain : Set H)
  M_closed : M.IsClosed
  M_generates : ∃ S : HilbertC0Semigroup H, IsMinusGenerator S M
  L_dense : ∀ k, Dense ((L k).domain : Set H)
  dom_le : ∀ k, M.domain ≤ (L k).domain
  L_relBdd : ∀ k, IsRelativelyBounded (L k) M (dom_le k)
  /-- (3)/(19) on dyads ρ = |φ⟩⟨ψ|, φ, ψ ∈ 𝒟(M): ρ ∈ 𝒟(ℒ) and
  ℒ(ρ) = Σ_k |L_kφ⟩⟨L_kψ| − |Mφ⟩⟨ψ| − |φ⟩⟨Mψ|, the sum converging in trace norm. -/
  eq3 : ∀ φ ψ : M.domain, ∃ ρ η : TraceClass H, ρ.val = dyad (φ : H) ψ ∧
    InTraceGeneratorGraph T ρ η ∧
    Tendsto (fun F : Finset κ => traceNormValue
        ((∑ k ∈ F, dyad (L k (Submodule.inclusion (dom_le k) φ))
            (L k (Submodule.inclusion (dom_le k) ψ)))
          - dyad (M φ) ψ - dyad (φ : H) (M ψ) - η.val))
      atTop (𝓝 0)
  /-- (4)/(20) as quadratic forms on 𝒟(M): Σ_k ‖L_kφ‖² = ⟨φ|Mφ⟩ + ⟨Mφ|φ⟩. -/
  eq4 : ∀ φ : M.domain, HasSum (fun k => ((‖L k (Submodule.inclusion (dom_le k) φ)‖ ^ 2 : ℝ) : ℂ))
    (inner ℂ (φ : H) (M φ) + inner ℂ (M φ) (φ : H))
  /-- p. 3: 𝒟(ℒ) is the graph-norm closure of 𝒟₀. -/
  core : IsCore T {ρ | ρ.val ∈ finiteDyads M.domain}

/-- (15) on a dyad: 𝓜(|φ⟩⟨ψ|) = M|φ⟩⟨ψ| + |φ⟩⟨ψ|M† = |Mφ⟩⟨ψ| + |φ⟩⟨Mψ|. -/
def GenStdForm.calM {T : TraceDynamicalSemigroup b} (S : GenStdForm T) (φ ψ : S.M.domain) :
    H →L[ℂ] H :=
  dyad (S.M φ) ψ + dyad (φ : H) (S.M ψ)

/-- The value ℒ(A) of the generator at an operator `A` in its domain (a chosen graph value;
0 off the domain). Used only inside `contractor` and `expander`. -/
def genOp (T : TraceDynamicalSemigroup b) (A : H →L[ℂ] H) : H →L[ℂ] H := by
  classical
  exact if h : ∃ ρ η : TraceClass H, ρ.val = A ∧ InTraceGeneratorGraph T ρ η
    then (Classical.choose (Classical.choose_spec h)).val else 0

/-- Definition 5, p. 5: 𝒟(M) = {ψ : |ψ⟩⟨χ| ∈ 𝒟(ℒ)}. -/
def contractorDomain (T : TraceDynamicalSemigroup b) (χ : H) : Set H :=
  {ψ | ∃ ρ ∈ TraceGeneratorDomain T, ρ.val = dyad ψ χ}

/-- Definition 5, (7): Mψ = −ℒ(|ψ⟩⟨χ|)χ + ½⟨χ|ℒ(|χ⟩⟨χ|)|χ⟩ψ. -/
def contractor (T : TraceDynamicalSemigroup b) (χ ψ : H) : H :=
  -(genOp T (dyad ψ χ)) χ + ((1 / 2 : ℂ) * inner ℂ χ (genOp T (dyad χ χ) χ)) • ψ

/-- (8) on dyads: ℒ₊(|φ⟩⟨ψ|) = ℒ(|φ⟩⟨ψ|) + |Mφ⟩⟨ψ| + |φ⟩⟨Mψ|, with M of Definition 5. -/
def expander (T : TraceDynamicalSemigroup b) (χ φ ψ : H) : H →L[ℂ] H :=
  genOp T (dyad φ ψ) + dyad (contractor T χ φ) ψ + dyad φ (contractor T χ ψ)

/-- Theorem 14, p. 15: sesquilinear forms with the common form domain 𝒟_f = lin{f_n}
(conjugate-linear in the first slot), "𝔔(ℋ)". -/
abbrev FormOn (f : HilbertBasis ℕ ℂ H) :=
  Submodule.span ℂ (Set.range f) →ₗ⋆[ℂ] Submodule.span ℂ (Set.range f) →ₗ[ℂ] ℂ

/-- Theorem 14, p. 15: `Q : 𝒟²_e → 𝔔(ℋ)` is completely positive: for every positive n×n block
(ρ_{ac}) of elements of 𝒟²_e and all g_1, …, g_n ∈ 𝒟_f, Σ_{a,c} ⟨g_a|Q(ρ_{ac})|g_c⟩ ≥ 0. -/
def IsFormCP (e f : HilbertBasis ℕ ℂ H) (Q : matrixUnits (Set.range e) →ₗ[ℂ] FormOn f) : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → Fin n → matrixUnits (Set.range e)),
    (∀ z : Fin n → H, 0 ≤ (∑ a, ∑ c, inner ℂ (z a) ((ρ a c : H →L[ℂ] H) (z c))).re ∧
      (∑ a, ∑ c, inner ℂ (z a) ((ρ a c : H →L[ℂ] H) (z c))).im = 0) →
    ∀ g : Fin n → Submodule.span ℂ (Set.range f),
      0 ≤ (∑ a, ∑ c, Q (ρ a c) (g a) (g c)).re ∧ (∑ a, ∑ c, Q (ρ a c) (g a) (g c)).im = 0

/-- p. 16, (24): the matrix unit E_{k,ℓ} = |e_k⟩⟨e_ℓ| as an element of 𝒟²_e. -/
def matrixUnit (e : HilbertBasis ℕ ℂ H) (k l : ℕ) : matrixUnits (Set.range e) :=
  ⟨dyad (e k) (e l), Submodule.subset_span ⟨e k, ⟨k, rfl⟩, e l, ⟨l, rfl⟩, rfl⟩⟩

end GenKraus.StdForm


