-- Prove2me | Definitions.Def_SemAC02_naiveRelPR
-- name    : SemAC02_naiveRelPR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:41.849481+00:00
-- url     : https://prove2.me/theorems/746cfc4a-504f-4e22-876d-08b9d245638e
-- title:
--   The naïve relative pseudo-reduction $R_{f,\ell}$
-- statement:
--   Let $S\subseteq\mathcal B_n$, $f\in\mathcal B_n$ and $\ell\ge0$. Let $D^{(f)}_\ell(S)$ be the space of polynomials admitting a PC derivation from $fS=\{fa:a\in S\}$ entirely in $f\mathcal B_n^{\le\ell}$ (every line lies in $f\mathcal B_n^{\le\ell}$). The **naïve relative pseudo-reduction** is the quotient map
--   $$
--   R_{f,\ell}: f\mathcal B_n^{\le\ell}\to f\mathcal B_n^{\le\ell}/D^{(f)}_\ell(S). \tag{9}
--   $$
--   It is non-zero precisely when $f$ has no such derivation.
--
--   **Formalization Note** PC derivations are the published `PCNonBool.IsDerivation` with reduction `AC02Frege.ML`. $D^{(f)}_\ell(S)$ is taken as the span of the derivable polynomials (they already form a subspace).
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), p.36, (9), p.36 (PDF p.38)

import Mathlib
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble

namespace SemAC02

/-- `u` admits a **PC derivation from `fS` entirely in `f B_n^{≤ℓ}`** (Alekseev–Gryaznov–Itsykson–
Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), p.36): a PC derivation in `B_n` from the axioms `{f a : a ∈ S}` containing `u`, every
line of which lies in `f B_n^{≤ℓ}`.

**Formalization Note** The derivation is the published `PCNonBool.IsDerivation` with reduction
`AC02Frege.ML` (lines are multilinear representatives in `B_n`). -/
def RelDerivable {σ : Type} (S : Set (MvPolynomial σ (ZMod 2))) (f : MvPolynomial σ (ZMod 2))
    (ℓ : ℕ) (u : MvPolynomial σ (ZMod 2)) : Prop :=
  ∃ τ : List (MvPolynomial σ (ZMod 2)),
    PCNonBool.IsDerivation AC02Frege.ML (mulML f '' S) τ ∧ (∀ w ∈ τ, w ∈ multSpace f ℓ) ∧ u ∈ τ

/-- The space `D_ℓ^{(f)}(S)` (p.36) as a subspace of `f B_n^{≤ℓ}`.

**Formalization Note** Taken as the span of the derivable polynomials; the paper notes that the
derivable polynomials already form a linear subspace, so the span adds nothing. -/
noncomputable def relDerivSpace {σ : Type} (S : Set (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) (ℓ : ℕ) : Submodule (ZMod 2) (multSpace f ℓ) :=
  Submodule.comap (multSpace f ℓ).subtype (Submodule.span (ZMod 2) {u | RelDerivable S f ℓ u})

/-- The **naïve relative pseudo-reduction** `R_{f,ℓ} : f B_n^{≤ℓ} → f B_n^{≤ℓ} / D_ℓ^{(f)}(S)`, the
quotient map (9) (p.36). -/
noncomputable def naiveRelPR {σ : Type} (S : Set (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) (ℓ : ℕ) :
    multSpace f ℓ →ₗ[ZMod 2] (multSpace f ℓ ⧸ relDerivSpace S f ℓ) :=
  (relDerivSpace S f ℓ).mkQ

end SemAC02


