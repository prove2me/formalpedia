-- Prove2me | Definitions.Def_DesignTest_Supplement_mubSet
-- name    : DesignTest_Supplement_mubSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:08:08.322927+00:00
-- url     : https://prove2.me/theorems/d420e2e3-128e-40a7-8065-6273e76fd4c0
-- title:
--   Maximally entangled MUB unitaries $\mathcal M_d$ up to phase
-- statement:
--   Let $F=\mathbb F_d$, $K=\mathbb F_{d^2}$ with an $F$-basis $e_1,e_2$, identify $|x_1e_1+x_2e_2\rangle$ with $|x_1\rangle\otimes|x_2\rangle$, and let $\chi$ be a nontrivial additive character of $K$. On $\mathbb C^{K}$ put $X(v)|x\rangle=|x+v\rangle$, $Z(u)|x\rangle=\chi(ux)|x\rangle$, $W(u,v)=Z(u)X(v)$. For $a\in K$ the commuting family $\{W(av,v):v\in K\}$ has a joint eigenbasis $B_a$; $d^2-d$ of these bases consist of maximally entangled vectors. Every maximally entangled $|\phi\rangle$ is $(I\otimes U_\phi)|\Phi_d\rangle$ for a unitary $U_\phi$, and
--
--   $$\mathcal M_d=\{U_\phi: |\phi\rangle\in B_a \text{ for a maximally entangled basis } B_a\},\qquad|\mathcal M_d|=d^3(d-1).$$
--
--   Up to phase, $V\in\mathcal M_d$ exactly when the Choi vector of $V$ is a joint eigenvector of $\{W(av,v)\}$ for some $a$. $\mu_{\mathrm{MUB}}$ is uniform on a list of phase representatives.
--
--   **Formalization Note.** The joint eigenspaces are one-dimensional; a Choi vector of a unitary is maximally entangled, so product bases contribute nothing. Another nontrivial character relabels $B_a$ and gives the same set.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §5.3, pp.60–62

import Mathlib
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open RandomGateDesign.MasterBound

/-- The **Choi vector** coordinate of `V ∈ U(d)` at the label `x ∈ F_{d²}`: under the identification
`|x₁e₁ + x₂e₂⟩ ↔ |x₁⟩ ⊗ |x₂⟩` (`x₁, x₂ ∈ F_d`, `e₁, e₂` an `F_d`-basis `b` of `F_{d²}`, `F_d` labelled by
`Fin d` through `e`), the vector `(I ⊗ V)|Φ_d⟩ ∝ Σ_i |i⟩ ⊗ V|i⟩` has coordinate `V_{x₂ x₁}` at
`|x₁⟩|x₂⟩` (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027
submission (sha256 e2f0a429…), §5.3, pp.60–62). The normalization `d^{-1/2}` is omitted. -/
noncomputable def choiCoord {F K : Type} [Field F] [Field K] [Algebra F K] {d : ℕ} (e : Fin d ≃ F)
    (b : Module.Basis (Fin 2) F K) (V : U d) (x : K) : ℂ :=
  (V : Matrix (Fin d) (Fin d) ℂ) (e.symm (b.repr x 1)) (e.symm (b.repr x 0))

/-- **The MUB unitaries `M_d` up to phase** (STOC 2027 submission (sha256 e2f0a429…), §5.3, pp.60–62).
On `ℂ^{F_{d²}}` put `X(v)|x⟩ = |x + v⟩`, `Z(u)|x⟩ = χ(u x)|x⟩` and `W(u, v) = Z(u) X(v)` for a nontrivial
additive character `χ` of `F_{d²}`; the bases `B_a` (`a ∈ F_{d²}`) are the joint eigenbases of the
commuting families `{W(a v, v) : v ∈ F_{d²}}`; `M_d` is the set of `U_ϕ` with `|ϕ⟩ = (I ⊗ U_ϕ)|Φ_d⟩` for
`|ϕ⟩` in one of the `d² − d` maximally entangled bases.

**Formalization Note.** `V` lies in the set iff its Choi vector is a joint eigenvector of
`W(a v, v)`, `v ∈ F_{d²}`, for some `a`: `χ(a v x) φ(x − v) = c φ(x)` for all `x`. The joint eigenspaces
are one-dimensional, so this says the Choi vector lies, up to phase, in `B_a`; a Choi vector of a unitary
is maximally entangled, so only the maximally entangled bases contribute, and the computational basis
`B_∞` contains no Choi vector of a unitary for `d ≥ 2`. The paper's trace character
`exp(2πi Tr_{F_{d²}/F_p}(z)/p)` is one nontrivial character; another one, `χ(c ·)`, relabels
`B_a ↦ B_{ca}` and gives the same set. The set is phase-closed; the list `M_d` of `d³(d − 1)` matrices is
a choice of representatives (`IsPhaseReps`). -/
def mubUpToPhase {F K : Type} [Field F] [Field K] [Algebra F K] {d : ℕ} (e : Fin d ≃ F)
    (b : Module.Basis (Fin 2) F K) (χ : AddChar K ℂ) : Set (U d) :=
  {V | ∃ a : K, ∀ v : K, ∃ c : ℂ, ∀ x : K,
    χ (a * v * x) * choiCoord e b V (x - v) = c * choiCoord e b V x}

end DesignTest.Supplement


