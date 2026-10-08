-- Prove2me | Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject
-- name    : KedlayaUmans_FrobeniusLift_LiftProject
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:32.957904+00:00
-- url     : https://prove2.me/theorems/8170d990-986e-4533-8fca-8ac637611539
-- title:
--   The lift φ : 𝔽_q^m → S via the interpolant g_α of (6.1), the projection π : S → R, g_α^{(i)}, and the Kronecker substitution f*
-- statement:
--   This file defines the maps of Section 6 of Kedlaya–Umans, on top of the rings $K = \mathbb F_p[W]/(P(W))$, $R = \mathbb F_q[W]/(P(W))$, the parameter $h = p^c$, the Frobenius powers $\sigma^i : x \mapsto x^{h^i}$ and the polynomial $E(Z) = Z^{h-1}-\eta$ of the companion file. Throughout, $\mathbb F_q$ is a finite field of characteristic $p$, $P$ is irreducible over $\mathbb F_p$, $\eta \in K$, and $m \ge 0$.
--
--   1. **The ring $S$.** $S = R[Z]/(E(Z))$.
--   2. **$\sigma^{-i}$ on $\mathbb F_q$.** On the finite field $\mathbb F_q$ the map $x \mapsto x^{h^i}$ is an automorphism; $\sigma^{-i} : \mathbb F_q \to \mathbb F_q$ denotes its inverse.
--   3. **The interpolant $g_\alpha$.** For $\alpha = (\alpha_0, \dots, \alpha_{m-1}) \in \mathbb F_q^m$, let $\ell_0, \dots, \ell_{m-1} \in K[Z]$ be the Lagrange basis polynomials for the nodes $\eta^0, \eta^1, \dots, \eta^{m-1}$ in the field $K$, and set
--   $$g_\alpha(Z) = \sum_{i=0}^{m-1} \sigma^{-i}(\alpha_i)\, \ell_i(Z) \in R[Z],$$
--   where the coefficients of $\ell_i$ are carried into $R$ by $K \subseteq R$ and $\sigma^{-i}(\alpha_i) \in \mathbb F_q \subseteq R$. When the nodes are distinct this is the polynomial of degree at most $m-1$ with $g_\alpha(\eta^i) = \sigma^{-i}(\alpha_i)$, as in Eq. (6.1).
--   4. **The lift.** $\varphi(\alpha) \in S$ is the residue class of $g_\alpha$ modulo $E$.
--   5. **The projection.** For $s \in S$, let $g(Z) \in R[Z]$ be its canonical representative, the remainder modulo the monic polynomial $E$ (degree less than $h-1$); then $\pi(s) = g(1) \in R$.
--   6. **The polynomials $g_\alpha^{(i)}$.** $g_\alpha^{(i)}(Z) = (g_\alpha(Z))^{h^i} \bmod E(Z)$.
--   7. **The Kronecker substitution.** For $f \in \mathbb F_q[X_0, \dots, X_{m-1}]$,
--   $$f^*(Y) = f\big(Y, Y^h, Y^{h^2}, \dots, Y^{h^{m-1}}\big) \in S[Y],$$
--   with the coefficients of $f$ viewed in $S$ through $\mathbb F_q \subseteq R \subseteq S$.
--
--   The identity $\pi(f^*(\varphi(\alpha))) = f(\alpha)$ of Lemma 6.1 relates these objects; it reduces evaluating the $m$-variate $f$ at $\alpha$ to evaluating the univariate $f^*$ at a point of $S$.
--
--   **Formalization Note** $\pi$ is not a ring homomorphism ($E(1) = 1 - \eta$ is in general nonzero), so it is defined through the canonical representative (`AdjoinRoot.modByMonicHom`), never through an arbitrary representative. The variables are indexed by `Fin m`, starting at $0$. The interpolant is given by the explicit Lagrange formula (Mathlib's `Lagrange.basis` over the field $K$, mapped coefficientwise into $R[Z]$), not by a characterization; that it satisfies (6.1) is the milestone theorem `eq_6_1`.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 19, Section 6 (definitions of σ, φ via Eq. (6.1), π, f* in Lemma 6.1, g_α^{(i)} in its proof)

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup

/-!
Kedlaya–Umans, *Fast polynomial factorization and modular composition*, Dagstuhl 08381
(version of Aug. 31, 2008), §6, p. 19: `σ^{-i}` on `𝔽_q`, the interpolant `g_α` of (6.1), the lift
`φ : 𝔽_q^m → S`, the projection `π : S → R`, the polynomials `g_α^{(i)} = g_α^{h^i} mod E`, and the
Kronecker substitution `f*(Y) = f(Y, Y^h, …, Y^{h^{m-1}})`.
-/

open Polynomial

namespace KedlayaUmans.FrobeniusLift

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p] (P : (ZMod p)[X])

/-- The ring `S = R[Z]/(E(Z))`. -/
abbrev S (η : K p P) : Type _ := AdjoinRoot (E p F P η)

/-- `σ^{-i}` on `𝔽_q`: the inverse of the automorphism `x ↦ x^{h^i}` of the finite field `F`. -/
noncomputable def sigmaInv (i : ℕ) : F ≃+* F :=
  (iterateFrobeniusEquiv F p (P.natDegree * i)).symm

/-- The interpolation nodes `η^0, η^1, …, η^{m-1}` in the field `𝔽_p[W]/(P(W))`. -/
noncomputable def node (m : ℕ) (η : K p P) (j : Fin m) : K p P :=
  η ^ (j : ℕ)

/-- The polynomial `g_α(Z) ∈ R[Z]` of (6.1): the Lagrange interpolant of degree at most `m - 1`
taking the value `σ^{-i}(α_i)` at `η^i` for `i = 0, …, m-1`. The Lagrange basis polynomials are
formed over the field `𝔽_p[W]/(P(W))` (where the node differences are invertible) and mapped
coefficientwise into `R[Z]`. -/
noncomputable def gAlpha [Fact (Irreducible P)] {m : ℕ} (η : K p P) (α : Fin m → F) :
    (R p F P)[X] :=
  ∑ i : Fin m, C (algebraMap F (R p F P) (sigmaInv p F P i (α i))) *
    (Lagrange.basis Finset.univ (node p P m η) i).map (ι p F P)

/-- The lift `φ : 𝔽_q^m → S`, `φ(α) =` the residue class of `g_α` modulo `E`. -/
noncomputable def phi [Fact (Irreducible P)] {m : ℕ} (η : K p P) (α : Fin m → F) : S p F P η :=
  AdjoinRoot.mk (E p F P η) (gAlpha p F P η α)

/-- The projection `π : S → R`: take the canonical representative `g(Z)` (the remainder modulo the
monic `E`, of degree `< h - 1`) and evaluate it at `Z = 1`. This is not a ring homomorphism. -/
noncomputable def pi [Fact (Irreducible P)] (η : K p P) (s : S p F P η) : R p F P :=
  (AdjoinRoot.modByMonicHom (E_monic p F P η) s).eval 1

/-- `g_α^{(i)}(Z) = (g_α(Z))^{h^i} mod E(Z)`. -/
noncomputable def gIter [Fact (Irreducible P)] {m : ℕ} (η : K p P) (α : Fin m → F) (i : ℕ) :
    (R p F P)[X] :=
  (gAlpha p F P η α ^ (h p P ^ i)) %ₘ E p F P η

/-- The Kronecker substitution `f*(Y) = f(Y, Y^h, Y^{h^2}, …, Y^{h^{m-1}}) ∈ S[Y]` of
`f ∈ 𝔽_q[X_0, …, X_{m-1}]`, with the coefficients of `f` viewed in `S` via `𝔽_q ⊆ R ⊆ S`. -/
noncomputable def fStar {m : ℕ} (η : K p P) (f : MvPolynomial (Fin m) F) : (S p F P η)[X] :=
  MvPolynomial.eval₂ (C.comp (algebraMap F (S p F P η))) (fun i : Fin m => X ^ (h p P ^ (i : ℕ))) f

end KedlayaUmans.FrobeniusLift


