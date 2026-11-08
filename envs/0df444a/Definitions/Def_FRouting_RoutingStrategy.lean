-- Prove2me | Definitions.Def_FRouting_RoutingStrategy
-- name    : FRouting_RoutingStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:59.029511+00:00
-- url     : https://prove2.me/theorems/bfc68c2f-a1d7-45c8-a846-bd1814ce329b
-- title:
--   $f$-routing strategies, the mid-protocol state and $(1-\varepsilon)$-correctness
-- statement:
--   A **routing strategy** for input length $n$ and qudit dimension $d$ consists of finite registers $L,R$; for each $x$ finite registers $A_1,B_2$; for each $y$ finite registers $B_1,A_2$; a density matrix on $LR$; Alice's channel $\mathcal U^x:QL\to A_1B_2$; Bob's channel $\mathcal V^y:R\to B_1A_2$; and, for all $(x,y,b)$, channels $\mathcal U^{xyb}:A_1A_2\to Q_0$ and $\mathcal V^{xyb}:B_1B_2\to Q_1$, with $Q,Q_0,Q_1$ of dimension $d$.
--
--   With $A=A_1A_2$ and $B=B_1B_2$, the protocol's states are
--   $$\rho_{\bar QQLR}=\Phi_{\bar QQ}\otimes(\text{resource}),\qquad (\rho^{xy})_{\bar QAB}=(\mathrm{id}_{\bar Q}\otimes\mathcal U^x\otimes\mathcal V^y)(\rho),$$
--   $$(\rho^{xyb})_{\bar QQ_0Q_1}=(\mathrm{id}_{\bar Q}\otimes\mathcal U^{xyb}\otimes\mathcal V^{xyb})(\rho^{xy}).$$
--   The strategy is **$(1-\varepsilon)$-correct on $(x,y)$** for $f$ if, with $b=f(x,y)$,
--   $$F\big((\rho^{xyb})_{\bar QQ_b},\Phi\big)\ge 1-\varepsilon ,$$
--   where $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$. Finally $F_0=F(\rho_{\bar QA},\rho_{\bar Q}\otimes\rho_A)$ and $F_1=F(\rho_{\bar QB},\rho_{\bar Q}\otimes\rho_B)$ for $\rho=\rho^{xy}$.
--
--   The partition into retained and outgoing registers depends only on the party's own input, so the mid-protocol state can be prepared without knowing $f(x,y)$.
--
--   **Formalization Note** Every finite channel is allowed here; resource bounds live in `UniformStrategy`. $F$ is the root fidelity: the paper fixes it by $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ (Theorem 6.9, p.25) and $\operatorname{tr}(\Phi\sigma)=F(\sigma,\Phi)^2$ (p.19).
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), §3.4, pp.15–16; §2, p.10

import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_FRouting_Phi
import Definitions.Def_FRouting_localTensor
import Definitions.Def_FRouting_margQA
import Definitions.Def_WildeQIT_fidelity

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace FRouting

open WildeQIT

/-- A finite register: a finite type with decidable equality, used for the systems of a strategy. -/
structure Reg where
  /-- The basis labels of the register. -/
  carrier : Type
  [instFintype : Fintype carrier]
  [instDecEq : DecidableEq carrier]

instance : CoeSort Reg Type := ⟨Reg.carrier⟩

attribute [instance] Reg.instFintype Reg.instDecEq

/-- **A routing strategy for input length `n` and qudit dimension `d`.** Renard, *Computational
Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), §3.4, pp.15–16: registers
`L, R`; a resource state on `LR`; Alice's channel `𝒰ˣ : QL → A₁B₂` and Bob's `𝒱ʸ : R → B₁A₂`; the
post-communication channels `𝒰ˣʸᵇ : A₁A₂ → Q₀` and `𝒱ˣʸᵇ : B₁B₂ → Q₁`.

**Formalization Note** Every finite channel is allowed: Theorem 1.9, p.6, says "a routing strategy",
with no resource bound; the bounds live in `UniformStrategy`. The partition into retained and
outgoing registers depends only on the party's own input (p.10): `A₁, B₂` on `x`, and `B₁, A₂` on
`y`. Only the post-communication channels see `(x, y, b)`. -/
structure RoutingStrategy (n d : ℕ) where
  /-- Alice's half `L` of the resource. -/
  L : Reg
  /-- Bob's half `R` of the resource. -/
  R : Reg
  /-- The register `A₁` that Alice retains. -/
  A₁ : (Fin n → Bool) → Reg
  /-- The register `B₂` that Alice sends to Bob. -/
  B₂ : (Fin n → Bool) → Reg
  /-- The register `B₁` that Bob retains. -/
  B₁ : (Fin n → Bool) → Reg
  /-- The register `A₂` that Bob sends to Alice. -/
  A₂ : (Fin n → Bool) → Reg
  /-- The adversaries' resource state on `LR`. -/
  resource : Matrix (L × R) (L × R) ℂ
  resource_density : PeresTerno.IsDensityMatrix resource
  /-- Alice's pre-communication channel `𝒰ˣ : QL → A₁B₂`. -/
  U : ∀ x, QChannel (Fin d × L) (A₁ x × B₂ x)
  /-- Bob's pre-communication channel `𝒱ʸ : R → B₁A₂`. -/
  V : ∀ y, QChannel R (B₁ y × A₂ y)
  /-- Alice's post-communication channel `𝒰ˣʸᵇ : A₁A₂ → Q₀`. -/
  Uₚ : ∀ x y, Bool → QChannel (A₁ x × A₂ y) (Fin d)
  /-- Bob's post-communication channel `𝒱ˣʸᵇ : B₁B₂ → Q₁`. -/
  Vₚ : ∀ x y, Bool → QChannel (B₁ y × B₂ x) (Fin d)

namespace RoutingStrategy

variable {n d : ℕ} (S : RoutingStrategy n d)

/-- The initial state `ρ_{Q̄QLR} = Φ_{Q̄Q} ⊗ (resource)` (p.16, step 1), with its registers regrouped
as `Q̄ × ((Q × L) × R)`. -/
noncomputable def initialState : Matrix (Fin d × ((Fin d × S.L) × S.R))
    (Fin d × ((Fin d × S.L) × S.R)) ℂ :=
  let g : Fin d × ((Fin d × S.L) × S.R) → (Fin d × Fin d) × (S.L × S.R) :=
    fun p => ((p.1, p.2.1.1), (p.2.1.2, p.2.2))
  (Phi d ⊗ₖ S.resource).submatrix g g

/-- **The mid-protocol state `(ρˣʸ)_{Q̄AB}`** (p.16, step 3):
`(id_{Q̄} ⊗ 𝒰ˣ ⊗ 𝒱ʸ)(ρ)`, with its registers written as `Q̄ × ((A₁ × A₂) × (B₁ × B₂))`, the grouping
after the exchange. The first register is always the reference `Q̄`. -/
noncomputable def midState (x y : Fin n → Bool) :
    Matrix (Fin d × ((S.A₁ x × S.A₂ y) × (S.B₁ y × S.B₂ x)))
      (Fin d × ((S.A₁ x × S.A₂ y) × (S.B₁ y × S.B₂ x))) ℂ :=
  let g : Fin d × ((S.A₁ x × S.A₂ y) × (S.B₁ y × S.B₂ x)) →
      Fin d × ((S.A₁ x × S.B₂ x) × (S.B₁ y × S.A₂ y)) :=
    fun p => (p.1, ((p.2.1.1, p.2.2.2), (p.2.2.1, p.2.1.2)))
  (localTensor (S.U x) (S.V y) S.initialState).submatrix g g

/-- **The final state `(ρˣʸᵇ)_{Q̄Q₀Q₁}`** (p.16, step 4), on `Q̄ × (Q₀ × Q₁)`. -/
noncomputable def finalState (x y : Fin n → Bool) (b : Bool) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  localTensor (S.Uₚ x y b) (S.Vₚ x y b) (S.midState x y)

/-- The state the verifiers test (Figure 2, p.16: "For b = f(x, y), the verifiers test `Q_b`"): the
marginal on `Q̄Q₀` of `ρˣʸᵇ` for `b = false`, the marginal on `Q̄Q₁` for `b = true`. -/
noncomputable def testedMarginal (x y : Fin n → Bool) :
    Bool → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
  | false => margQA (S.finalState x y false)
  | true => margQB (S.finalState x y true)

/-- **`(1 − ε)`-correct on input `(x, y)`** (p.16):
`F((ρˣʸᵇ)_{Q̄Q_{f(x,y)}}, Φ) ≥ 1 − ε`, with `b = f(x, y)`.

**Formalization Note** `F` is the root fidelity `‖√ρ√σ‖₁`, as in Theorem 6.9, p.25, and in
`tr(Φσ) = F(σ, Φ)²`, p.19. The squared fidelity would change every constant of §4. -/
def IsCorrectOn (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (ε : ℝ) (x y : Fin n → Bool) : Prop :=
  1 - ε ≤ rootFidelity (S.testedMarginal x y (f x y)) (Phi d)

/-- `F₀ := F(ρ_{Q̄A}, ρ_{Q̄} ⊗ ρ_A)` for the mid-protocol state (Theorem 4.1, p.17; Theorem 1.9, p.6). -/
noncomputable def F0 (x y : Fin n → Bool) : ℝ :=
  rootFidelity (margQA (S.midState x y)) (margQ (S.midState x y) ⊗ₖ margA (S.midState x y))

/-- `F₁ := F(ρ_{Q̄B}, ρ_{Q̄} ⊗ ρ_B)` for the mid-protocol state (Theorem 4.1, p.17). -/
noncomputable def F1 (x y : Fin n → Bool) : ℝ :=
  rootFidelity (margQB (S.midState x y)) (margQ (S.midState x y) ⊗ₖ margB (S.midState x y))

end RoutingStrategy

end FRouting


