-- Prove2me | Definitions.Def_InfoDerivQT_framework
-- name    : InfoDerivQT_framework
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T05:25:21.205881+00:00
-- url     : https://prove2.me/theorems/28e4f294-9e8a-46ef-bbbb-b0f46a3c21ae
-- title:
--   Operational-probabilistic theories (finite-dimensional, quotiented framework)
-- statement:
--   An **operational-probabilistic theory** (Sec. II of the paper), presented after operational equivalence classes have been taken and in finite dimension.
--
--   It consists of a type of **systems**, a composite system $AB$ for every pair $A,B$, and a **size** $D_A\in\mathbb N$ for each system; the space $\mathrm{St}_{\mathbb R}(A)$ is modelled as $\mathbb R^{D_A}$. For every finite outcome set $X$ the theory specifies which families $\{\rho_i\}_{i\in X}\subset\mathbb R^{D_A}$ are **preparation tests**, which families of linear functionals $\{a_j\}_{j\in X}$ are **observation tests**, and which families of linear maps $\{\mathcal C_i\}_{i\in X}:\mathbb R^{D_A}\to\mathbb R^{D_B}$ are **tests** from $A$ to $B$. It also provides bilinear parallel compositions $\rho\otimes\sigma$, $a\otimes b$, $\mathcal C\otimes\mathcal D$, the induced states $(a|_A|\Psi)_{AB}$ and $(b|_B|\Psi)_{AB}$, a swap $AB\to BA$ and an associator $(AB)C\to A(BC)$ with inverse. These data satisfy:
--
--   1. the probability rule (2): $(a_j|\rho_i)\ge 0$ and $\sum_{i,j}(a_j|\rho_i)=1$, and the product rule (3): $(a\otimes b|\rho\otimes\sigma)=(a|\rho)(b|\sigma)$;
--   2. states span $\mathbb R^{D_A}$, effects span its dual, every system has an observation test, and the set of states is closed;
--   3. closure of tests under coarse-graining, identity, sequential composition with classical control, classical randomization, parallel composition, and conditioning on one side of a bipartite preparation; every nonzero state is a positive multiple of a deterministic state;
--   4. the circuit coherences: $(b|\,(a|_A\Psi)=(a\otimes b|\Psi)$ (and symmetrically), $(\mathcal C\otimes\mathcal D)(\rho\otimes\sigma)=\mathcal C\rho\otimes\mathcal D\sigma$, $(a\otimes b)\circ(\mathcal C\otimes\mathcal D)=(a\circ\mathcal C)\otimes(b\circ\mathcal D)$, $\mathcal I\otimes\mathcal I=\mathcal I$, functoriality of $\otimes$, and the swap/associator are deterministic tests acting on product states in the expected way, with the swap an involution and the associator invertible.
--
--   On top of the structure the file defines: the sets $\mathrm{St}(A)$, $\mathrm{Eff}(A)$, $\mathrm{Transf}(A,B)$; normalized states $\mathrm{St}_1(A)$, deterministic effects and channels (single-outcome tests); refinements; **pure** states and **atomic** effects and transformations (every refinement is $p$ times the object, $p\ge0$); **completely mixed** states (Definition 1); **reversible** transformations (Definition 2); operational equivalence (Definition 3); the **face** $F_\rho$ (Definition 4); **perfectly distinguishable** families (Definition 5); **maximal** perfectly distinguishable families (Definition 6) and maximal families of pure states.
--
--   **Formalization Note** Transformations are identified with their action on single-system states; under local distinguishability this agrees with the paper's equivalence relation (Eq. (5)). The trivial system is not modelled; states and effects are separate sorts.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), pp. 012311-3 to 012311-7, Sec. II (framework; Eqs. (2), (3), (5)), Definitions 1–6 (pp. 012311-5, -6, -7, -13, -14)

import Mathlib

/-!
Framework of (finite-dimensional, operationally-quotiented) operational-probabilistic
theories, following Sec. II of Chiribella, D'Ariano, Perinotti,
"Informational derivation of quantum theory", Phys. Rev. A 84, 012311 (2011).
-/

namespace InfoDerivQT

/-- Coordinate model of the real vector space `St_ℝ(A)` of a system of size `n`. -/
abbrev Vec (n : ℕ) : Type := Fin n → ℝ

/-- An operational-probabilistic theory (Sec. II of the paper), presented after the
operational equivalence classes have been taken: states of a system `A` are vectors in
`St_ℝ(A) = ℝ^{D_A}`, effects are linear functionals on it, and transformations from `A`
to `B` are linear maps `St_ℝ(A) → St_ℝ(B)`. Tests are finite families of such objects,
indexed by a finite outcome set. -/
structure OPT : Type 1 where
  /-- The systems of the theory. -/
  Sys : Type
  /-- The composite system `AB`. -/
  comp : Sys → Sys → Sys
  /-- The size `D_A = dim St_ℝ(A)`. -/
  size : Sys → ℕ
  /-- Preparation tests `{ρᵢ}_{i ∈ X}` of system `A`. -/
  PrepTest : (A : Sys) → (X : Type) → [Fintype X] → Set (X → Vec (size A))
  /-- Observation tests `{aⱼ}_{j ∈ Y}` of system `A`. -/
  ObsTest : (A : Sys) → (X : Type) → [Fintype X] → Set (X → Module.Dual ℝ (Vec (size A)))
  /-- Tests `{Cᵢ}_{i ∈ X}` from system `A` to system `B`. -/
  Test : (A B : Sys) → (X : Type) → [Fintype X] →
    Set (X → (Vec (size A) →ₗ[ℝ] Vec (size B)))
  /-- Parallel composition of states, `ρ ⊗ σ`. -/
  tensorSt : {A B : Sys} → Vec (size A) →ₗ[ℝ] Vec (size B) →ₗ[ℝ] Vec (size (comp A B))
  /-- Parallel composition of effects, `a ⊗ b`. -/
  tensorEff : {A B : Sys} → Module.Dual ℝ (Vec (size A)) →ₗ[ℝ]
    Module.Dual ℝ (Vec (size B)) →ₗ[ℝ] Module.Dual ℝ (Vec (size (comp A B)))
  /-- Parallel composition of transformations, `C ⊗ D`. -/
  tensorT : {A B A' B' : Sys} → (Vec (size A) →ₗ[ℝ] Vec (size B)) →ₗ[ℝ]
    (Vec (size A') →ₗ[ℝ] Vec (size B')) →ₗ[ℝ]
    (Vec (size (comp A A')) →ₗ[ℝ] Vec (size (comp B B')))
  /-- The unnormalized state `(a|_A |Ψ)_{AB}` of `B` induced by the effect `a` on `A`. -/
  condL : {A B : Sys} → Module.Dual ℝ (Vec (size A)) →ₗ[ℝ]
    (Vec (size (comp A B)) →ₗ[ℝ] Vec (size B))
  /-- The unnormalized state `(b|_B |Ψ)_{AB}` of `A` induced by the effect `b` on `B`. -/
  condR : {A B : Sys} → Module.Dual ℝ (Vec (size B)) →ₗ[ℝ]
    (Vec (size (comp A B)) →ₗ[ℝ] Vec (size A))
  /-- The swap `AB → BA`. -/
  swap : (A B : Sys) → Vec (size (comp A B)) →ₗ[ℝ] Vec (size (comp B A))
  /-- The associator `(AB)C → A(BC)`. -/
  assoc : (A B C : Sys) → Vec (size (comp (comp A B) C)) →ₗ[ℝ] Vec (size (comp A (comp B C)))
  /-- The inverse associator `A(BC) → (AB)C`. -/
  assocInv : (A B C : Sys) →
    Vec (size (comp A (comp B C))) →ₗ[ℝ] Vec (size (comp (comp A B) C))
  -- Probabilistic structure, Eq. (2).
  prob_nonneg : ∀ (A : Sys) (X Y : Type) [Fintype X] [Fintype Y]
    (ρ : X → Vec (size A)) (a : Y → Module.Dual ℝ (Vec (size A))),
    ρ ∈ PrepTest A X → a ∈ ObsTest A Y → ∀ i j, 0 ≤ a j (ρ i)
  prob_sum : ∀ (A : Sys) (X Y : Type) [Fintype X] [Fintype Y]
    (ρ : X → Vec (size A)) (a : Y → Module.Dual ℝ (Vec (size A))),
    ρ ∈ PrepTest A X → a ∈ ObsTest A Y → ∑ i, ∑ j, a j (ρ i) = 1
  -- Product rule, Eq. (3).
  tensor_prob : ∀ {A B : Sys} (a : Module.Dual ℝ (Vec (size A)))
    (b : Module.Dual ℝ (Vec (size B))) (ρ : Vec (size A)) (σ : Vec (size B)),
    tensorEff a b (tensorSt ρ σ) = a ρ * b σ
  -- Equivalence classes have been taken; finite dimension `D_A`.
  states_span : ∀ A : Sys, Submodule.span ℝ
    {ρ | ∃ (X : Type) (_ : Fintype X) (t : X → Vec (size A)) (i : X),
      t ∈ PrepTest A X ∧ t i = ρ} = ⊤
  effects_span : ∀ A : Sys, Submodule.span ℝ
    {a | ∃ (X : Type) (_ : Fintype X) (t : X → Module.Dual ℝ (Vec (size A))) (i : X),
      t ∈ ObsTest A X ∧ t i = a} = ⊤
  /-- The set of states is closed (in the operational norm; all norms are equivalent). -/
  states_closed : ∀ A : Sys, IsClosed
    {ρ | ∃ (X : Type) (_ : Fintype X) (t : X → Vec (size A)) (i : X),
      t ∈ PrepTest A X ∧ t i = ρ}
  /-- Every system admits at least one observation test. -/
  obs_nonempty : ∀ A : Sys, ∃ (X : Type) (_ : Fintype X) (t : X → Module.Dual ℝ (Vec (size A))),
    t ∈ ObsTest A X
  -- Coarse graining (joining outcomes; with a bijection, relabelling).
  prep_coarse : ∀ (A : Sys) (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq Y]
    (t : X → Vec (size A)) (f : X → Y), t ∈ PrepTest A X →
    (fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), t x) ∈ PrepTest A Y
  obs_coarse : ∀ (A : Sys) (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq Y]
    (t : X → Module.Dual ℝ (Vec (size A))) (f : X → Y), t ∈ ObsTest A X →
    (fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), t x) ∈ ObsTest A Y
  test_coarse : ∀ (A B : Sys) (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq Y]
    (t : X → (Vec (size A) →ₗ[ℝ] Vec (size B))) (f : X → Y), t ∈ Test A B X →
    (fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), t x) ∈ Test A B Y
  -- Identity test.
  id_test : ∀ A : Sys, (fun _ : Unit => (LinearMap.id : Vec (size A) →ₗ[ℝ] Vec (size A)))
    ∈ Test A A Unit
  -- Sequential composition, with classical control (the second test may depend on the
  -- outcome of the first); the constant choice gives plain sequential composition.
  prep_then_test : ∀ (A B : Sys) (X : Type) [Fintype X] (Y : X → Type)
    [∀ i, Fintype (Y i)] (ρ : X → Vec (size A))
    (C : (i : X) → Y i → (Vec (size A) →ₗ[ℝ] Vec (size B))),
    ρ ∈ PrepTest A X → (∀ i, C i ∈ Test A B (Y i)) →
    (fun p : (Σ i, Y i) => C p.1 p.2 (ρ p.1)) ∈ PrepTest B (Σ i, Y i)
  test_then_obs : ∀ (A B : Sys) (X : Type) [Fintype X] (Y : X → Type)
    [∀ i, Fintype (Y i)] (C : X → (Vec (size A) →ₗ[ℝ] Vec (size B)))
    (b : (i : X) → Y i → Module.Dual ℝ (Vec (size B))),
    C ∈ Test A B X → (∀ i, b i ∈ ObsTest B (Y i)) →
    (fun p : (Σ i, Y i) => (b p.1 p.2).comp (C p.1)) ∈ ObsTest A (Σ i, Y i)
  test_then_test : ∀ (A B C : Sys) (X : Type) [Fintype X] (Y : X → Type)
    [∀ i, Fintype (Y i)] (D : X → (Vec (size A) →ₗ[ℝ] Vec (size B)))
    (E : (i : X) → Y i → (Vec (size B) →ₗ[ℝ] Vec (size C))),
    D ∈ Test A B X → (∀ i, E i ∈ Test B C (Y i)) →
    (fun p : (Σ i, Y i) => (E p.1 p.2).comp (D p.1)) ∈ Test A C (Σ i, Y i)
  -- Classical randomization: a test may be chosen at random according to a probability
  -- distribution `p` on `X` (combined with conditioning, this gives convex mixtures).
  prep_random : ∀ (A : Sys) (X : Type) [Fintype X] (Y : X → Type) [∀ i, Fintype (Y i)]
    (p : X → ℝ) (ρ : (i : X) → Y i → Vec (size A)),
    (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → (∀ i, ρ i ∈ PrepTest A (Y i)) →
    (fun q : (Σ i, Y i) => p q.1 • ρ q.1 q.2) ∈ PrepTest A (Σ i, Y i)
  obs_random : ∀ (A : Sys) (X : Type) [Fintype X] (Y : X → Type) [∀ i, Fintype (Y i)]
    (p : X → ℝ) (a : (i : X) → Y i → Module.Dual ℝ (Vec (size A))),
    (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → (∀ i, a i ∈ ObsTest A (Y i)) →
    (fun q : (Σ i, Y i) => p q.1 • a q.1 q.2) ∈ ObsTest A (Σ i, Y i)
  test_random : ∀ (A B : Sys) (X : Type) [Fintype X] (Y : X → Type) [∀ i, Fintype (Y i)]
    (p : X → ℝ) (C : (i : X) → Y i → (Vec (size A) →ₗ[ℝ] Vec (size B))),
    (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → (∀ i, C i ∈ Test A B (Y i)) →
    (fun q : (Σ i, Y i) => p q.1 • C q.1 q.2) ∈ Test A B (Σ i, Y i)
  /-- Rescaled preparations: every nonzero state is proportional to a deterministic
  (single-outcome) state. -/
  state_rescale : ∀ (A : Sys) (X : Type) [Fintype X] (t : X → Vec (size A)) (i : X),
    t ∈ PrepTest A X → t i ≠ 0 → ∃ c : ℝ, 0 < c ∧ (fun _ : Unit => c • t i) ∈ PrepTest A Unit
  -- Parallel composition of tests.
  prep_tensor : ∀ (A B : Sys) (X Y : Type) [Fintype X] [Fintype Y]
    (ρ : X → Vec (size A)) (σ : Y → Vec (size B)),
    ρ ∈ PrepTest A X → σ ∈ PrepTest B Y →
    (fun p : X × Y => tensorSt (ρ p.1) (σ p.2)) ∈ PrepTest (comp A B) (X × Y)
  obs_tensor : ∀ (A B : Sys) (X Y : Type) [Fintype X] [Fintype Y]
    (a : X → Module.Dual ℝ (Vec (size A))) (b : Y → Module.Dual ℝ (Vec (size B))),
    a ∈ ObsTest A X → b ∈ ObsTest B Y →
    (fun p : X × Y => tensorEff (a p.1) (b p.2)) ∈ ObsTest (comp A B) (X × Y)
  test_tensor : ∀ (A B A' B' : Sys) (X Y : Type) [Fintype X] [Fintype Y]
    (C : X → (Vec (size A) →ₗ[ℝ] Vec (size B))) (D : Y → (Vec (size A') →ₗ[ℝ] Vec (size B'))),
    C ∈ Test A B X → D ∈ Test A' B' Y →
    (fun p : X × Y => tensorT (C p.1) (D p.2)) ∈ Test (comp A A') (comp B B') (X × Y)
  -- Observation on one side of a bipartite preparation test leaves a preparation test.
  prep_condL : ∀ (A B : Sys) (X Y : Type) [Fintype X] [Fintype Y]
    (Ψ : X → Vec (size (comp A B))) (a : Y → Module.Dual ℝ (Vec (size A))),
    Ψ ∈ PrepTest (comp A B) X → a ∈ ObsTest A Y →
    (fun p : X × Y => condL (a p.2) (Ψ p.1)) ∈ PrepTest B (X × Y)
  prep_condR : ∀ (A B : Sys) (X Y : Type) [Fintype X] [Fintype Y]
    (Ψ : X → Vec (size (comp A B))) (b : Y → Module.Dual ℝ (Vec (size B))),
    Ψ ∈ PrepTest (comp A B) X → b ∈ ObsTest B Y →
    (fun p : X × Y => condR (b p.2) (Ψ p.1)) ∈ PrepTest A (X × Y)
  -- Coherence of the circuit rules.
  condL_spec : ∀ {A B : Sys} (a : Module.Dual ℝ (Vec (size A)))
    (b : Module.Dual ℝ (Vec (size B))) (Ψ : Vec (size (comp A B))),
    b (condL a Ψ) = tensorEff a b Ψ
  condR_spec : ∀ {A B : Sys} (a : Module.Dual ℝ (Vec (size A)))
    (b : Module.Dual ℝ (Vec (size B))) (Ψ : Vec (size (comp A B))),
    a (condR b Ψ) = tensorEff a b Ψ
  tensorT_tensorSt : ∀ {A B A' B' : Sys} (C : Vec (size A) →ₗ[ℝ] Vec (size B))
    (D : Vec (size A') →ₗ[ℝ] Vec (size B')) (ρ : Vec (size A)) (σ : Vec (size A')),
    tensorT C D (tensorSt ρ σ) = tensorSt (C ρ) (D σ)
  tensorEff_tensorT : ∀ {A B A' B' : Sys} (C : Vec (size A) →ₗ[ℝ] Vec (size B))
    (D : Vec (size A') →ₗ[ℝ] Vec (size B')) (a : Module.Dual ℝ (Vec (size B)))
    (b : Module.Dual ℝ (Vec (size B'))),
    (tensorEff a b).comp (tensorT C D) = tensorEff (a.comp C) (b.comp D)
  tensorT_id : ∀ (A B : Sys), tensorT (A := A) (B := A) (A' := B) (B' := B)
    (LinearMap.id : Vec (size A) →ₗ[ℝ] Vec (size A))
    (LinearMap.id : Vec (size B) →ₗ[ℝ] Vec (size B)) = LinearMap.id
  tensorT_comp : ∀ {A B C A' B' C' : Sys} (D : Vec (size B) →ₗ[ℝ] Vec (size C))
    (C₁ : Vec (size A) →ₗ[ℝ] Vec (size B)) (D' : Vec (size B') →ₗ[ℝ] Vec (size C'))
    (C₁' : Vec (size A') →ₗ[ℝ] Vec (size B')),
    tensorT (D.comp C₁) (D'.comp C₁') = (tensorT D D').comp (tensorT C₁ C₁')
  -- Swap and associator are deterministic (single-outcome) tests acting as expected on
  -- product states.
  swap_test : ∀ A B : Sys, (fun _ : Unit => swap A B) ∈ Test (comp A B) (comp B A) Unit
  swap_tensorSt : ∀ (A B : Sys) (ρ : Vec (size A)) (σ : Vec (size B)),
    swap A B (tensorSt ρ σ) = tensorSt σ ρ
  swap_swap : ∀ A B : Sys, (swap B A).comp (swap A B) = LinearMap.id
  assoc_test : ∀ A B C : Sys, (fun _ : Unit => assoc A B C) ∈
    Test (comp (comp A B) C) (comp A (comp B C)) Unit
  assocInv_test : ∀ A B C : Sys, (fun _ : Unit => assocInv A B C) ∈
    Test (comp A (comp B C)) (comp (comp A B) C) Unit
  assoc_tensorSt : ∀ (A B C : Sys) (ρ : Vec (size A)) (σ : Vec (size B)) (τ : Vec (size C)),
    assoc A B C (tensorSt (tensorSt ρ σ) τ) = tensorSt ρ (tensorSt σ τ)
  assoc_assocInv : ∀ A B C : Sys, (assoc A B C).comp (assocInv A B C) = LinearMap.id
  assocInv_assoc : ∀ A B C : Sys, (assocInv A B C).comp (assoc A B C) = LinearMap.id

namespace OPT

variable (T : OPT)

/-- `St(A)`: the states of `A` (members of some preparation test). -/
def St (A : T.Sys) : Set (Vec (T.size A)) :=
  {ρ | ∃ (X : Type) (_ : Fintype X) (t : X → Vec (T.size A)) (i : X),
    t ∈ T.PrepTest A X ∧ t i = ρ}

/-- `Eff(A)`: the effects of `A` (members of some observation test). -/
def Eff (A : T.Sys) : Set (Module.Dual ℝ (Vec (T.size A))) :=
  {a | ∃ (X : Type) (_ : Fintype X) (t : X → Module.Dual ℝ (Vec (T.size A))) (i : X),
    t ∈ T.ObsTest A X ∧ t i = a}

/-- `Transf(A,B)`: the transformations from `A` to `B` (members of some test). -/
def Transf (A B : T.Sys) : Set (Vec (T.size A) →ₗ[ℝ] Vec (T.size B)) :=
  {C | ∃ (X : Type) (_ : Fintype X) (t : X → (Vec (T.size A) →ₗ[ℝ] Vec (T.size B))) (i : X),
    t ∈ T.Test A B X ∧ t i = C}

/-- `St₁(A)`: the deterministic (normalized) states, i.e. single-outcome preparation tests. -/
def St1 (A : T.Sys) : Set (Vec (T.size A)) :=
  {ρ | (fun _ : Unit => ρ) ∈ T.PrepTest A Unit}

/-- Deterministic effects, i.e. single-outcome observation tests. -/
def DetEff (A : T.Sys) : Set (Module.Dual ℝ (Vec (T.size A))) :=
  {e | (fun _ : Unit => e) ∈ T.ObsTest A Unit}

/-- Channels: deterministic transformations, i.e. single-outcome tests. -/
def Channel (A B : T.Sys) : Set (Vec (T.size A) →ₗ[ℝ] Vec (T.size B)) :=
  {C | (fun _ : Unit => C) ∈ T.Test A B Unit}

/-- `σ` is a refinement of the state `ρ`: there are a preparation test `{ρᵢ}_{i∈X}` and a
subset `X₀ ⊆ X` with `ρ = ∑_{i∈X₀} ρᵢ` and `σ = ρᵢ` for some `i ∈ X₀`. -/
def IsRefinementSt (A : T.Sys) (σ ρ : Vec (T.size A)) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (t : X → Vec (T.size A)) (X₀ : Finset X),
    t ∈ T.PrepTest A X ∧ ρ = ∑ i ∈ X₀, t i ∧ ∃ i ∈ X₀, t i = σ

/-- Refinement of an effect. -/
def IsRefinementEff (A : T.Sys) (b a : Module.Dual ℝ (Vec (T.size A))) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (t : X → Module.Dual ℝ (Vec (T.size A))) (X₀ : Finset X),
    t ∈ T.ObsTest A X ∧ a = ∑ i ∈ X₀, t i ∧ ∃ i ∈ X₀, t i = b

/-- Refinement of a transformation. -/
def IsRefinementT (A B : T.Sys) (D C : Vec (T.size A) →ₗ[ℝ] Vec (T.size B)) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (t : X → (Vec (T.size A) →ₗ[ℝ] Vec (T.size B)))
    (X₀ : Finset X), t ∈ T.Test A B X ∧ C = ∑ i ∈ X₀, t i ∧ ∃ i ∈ X₀, t i = D

/-- A pure (atomic) state: a state with only trivial refinements `σ = p ρ`, `p ≥ 0`. -/
def IsPure (A : T.Sys) (ρ : Vec (T.size A)) : Prop :=
  ρ ∈ T.St A ∧ ∀ σ, T.IsRefinementSt A σ ρ → ∃ p : ℝ, 0 ≤ p ∧ σ = p • ρ

/-- An atomic effect. -/
def IsAtomicEff (A : T.Sys) (a : Module.Dual ℝ (Vec (T.size A))) : Prop :=
  a ∈ T.Eff A ∧ ∀ b, T.IsRefinementEff A b a → ∃ p : ℝ, 0 ≤ p ∧ b = p • a

/-- An atomic transformation. -/
def IsAtomicT (A B : T.Sys) (C : Vec (T.size A) →ₗ[ℝ] Vec (T.size B)) : Prop :=
  C ∈ T.Transf A B ∧ ∀ D, T.IsRefinementT A B D C → ∃ p : ℝ, 0 ≤ p ∧ D = p • C

/-- Definition 1: `ω` is completely mixed if for every state `ρ` there is `p > 0` such that
`p ρ` is a refinement of `ω`. -/
def IsCompletelyMixed (A : T.Sys) (ω : Vec (T.size A)) : Prop :=
  ω ∈ T.St A ∧ ∀ ρ ∈ T.St A, ∃ p : ℝ, 0 < p ∧ T.IsRefinementSt A (p • ρ) ω

/-- Definition 2: a reversible transformation from `A` to `B`. -/
def IsReversible (A B : T.Sys) (U : Vec (T.size A) →ₗ[ℝ] Vec (T.size B)) : Prop :=
  U ∈ T.Transf A B ∧ ∃ V ∈ T.Transf B A, V.comp U = LinearMap.id ∧ U.comp V = LinearMap.id

/-- Definition 3: operationally equivalent systems. -/
def OperationallyEquivalent (A B : T.Sys) : Prop :=
  ∃ U, T.IsReversible A B U

/-- Definition 4: the face `F_ρ` identified by a normalized state `ρ`. -/
def face (A : T.Sys) (ρ : Vec (T.size A)) : Set (Vec (T.size A)) :=
  {σ | σ ∈ T.St1 A ∧ ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∃ τ ∈ T.St1 A, ρ = p • σ + (1 - p) • τ}

/-- Definition 5: the normalized states `ρ₁, …, ρ_N` are perfectly distinguishable: there is an
observation test `{aⱼ}_{j=1}^N` with `(aⱼ|ρᵢ) = δᵢⱼ`. -/
def PerfectlyDistinguishable (A : T.Sys) {N : ℕ} (ρ : Fin N → Vec (T.size A)) : Prop :=
  (∀ i, ρ i ∈ T.St1 A) ∧ ∃ a : Fin N → Module.Dual ℝ (Vec (T.size A)),
    a ∈ T.ObsTest A (Fin N) ∧ ∀ i j, a j (ρ i) = if i = j then 1 else 0

/-- Definition 6: a perfectly distinguishable family is maximal if no normalized state can be
added keeping the family perfectly distinguishable. -/
def IsMaximalPerfDist (A : T.Sys) {N : ℕ} (ρ : Fin N → Vec (T.size A)) : Prop :=
  T.PerfectlyDistinguishable A ρ ∧
    ∀ σ ∈ T.St1 A, ¬ T.PerfectlyDistinguishable A (Fin.snoc ρ σ : Fin (N + 1) → _)

/-- A maximal set of perfectly distinguishable pure states. -/
def IsMaximalPerfDistPure (A : T.Sys) {N : ℕ} (ρ : Fin N → Vec (T.size A)) : Prop :=
  T.IsMaximalPerfDist A ρ ∧ ∀ i, T.IsPure A (ρ i)

end OPT

end InfoDerivQT


