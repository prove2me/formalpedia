-- Prove2me | Definitions.Def_QMAvsQCMAH_IsCSI
-- name    : QMAvsQCMAH_IsCSI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:47.52793+00:00
-- url     : https://prove2.me/theorems/192863f9-5e9f-4ce2-b221-5589c844baf7
-- title:
--   $\gamma$-contractive simultaneous incompressibility
-- statement:
--   Let $F_\lambda\subseteq\mathcal X_\lambda$ be random and $\gamma(\lambda)\to\infty$; put $\varepsilon_{\mathrm{inc}}(\lambda)=2^{-8\lambda^2}$ and $t_{\mathrm{inc}}(\lambda,c)=\lceil(c+8\lambda^2)/\gamma(\lambda)\rceil$. The family $(F_\lambda)$ satisfies **$\gamma$-contractive simultaneous incompressibility** if, for every polynomially bounded $c(\lambda)\ge0$ and all sufficiently large $\lambda$, every unbounded sender $w\leftarrow\mathrm{Enc}(F_\lambda,r)\in\{0,1\}^{c(\lambda)}$ and receiver $G(w,r)$ sharing a random tape $r$ independent of $F_\lambda$ satisfy
--   $$\Pr_{F_\lambda,r}[G(\mathrm{Enc}(F_\lambda,r),r)\text{ outputs }t_{\mathrm{inc}}(\lambda,c(\lambda))\text{ distinct elements of }F_\lambda]\le\varepsilon_{\mathrm{inc}}(\lambda).$$
--
--   **Formalization Note.** The tape ranges over any finite probability space; the receiver's other randomness and auxiliary data are part of the tape.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Section 4.2, p.28; Definition 18, pp.28–29, Equation (20)

import Definitions.Def_QMAvsQCMAH_PolyBounded
import Definitions.Def_QMAvsQCMAH_prob

set_option autoImplicit false

namespace QMAvsQCMAH

open Filter

/-- The incompressibility error `ε_inc(λ) = 2^{−8λ²}`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Section 4.2, p.28 (PDF p.31): "we fix the error εinc(λ) = 2^{−8λ²}". -/
noncomputable def epsInc (lam : ℕ) : ℝ := (2 : ℝ) ^ (-(8 * (lam : ℝ) ^ 2))

/-- The recovery threshold `t_inc(λ, c) = ⌈(c + 8λ²)/γ(λ)⌉`. -/
noncomputable def tinc (γ : ℕ → ℝ) (lam c : ℕ) : ℕ :=
  Nat.ceil (((c : ℝ) + 8 * (lam : ℝ) ^ 2) / γ lam)

/-- **γ-contractive simultaneous incompressibility** of random sets `F_λ ⊆ X_λ` (law `F λ`):
`γ(λ) → ∞`, and for every polynomially bounded `c(λ) ≥ 0` and all sufficiently large `λ`, every
unbounded sender `Enc(F_λ, r) ∈ {0,1}^{c(λ)}` and receiver `G(w, r)` sharing a random tape `r`
independent of `F_λ` satisfy
`Pr_{F_λ, r}[G(Enc(F_λ, r), r) outputs t_inc(λ, c(λ)) distinct elements of F_λ] ≤ ε_inc(λ)`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 18, pp.28–29 (PDF pp.31–32), Equation (20): "Fix γ : N → R>0 with γ(λ) → ∞ and
define the recovery threshold tinc(λ, c) = ⌈(c + 8λ²)/γ(λ)⌉. The family (Fλ)λ satisfies
γ-contractive simultaneous incompressibility if, for every polynomially bounded integer-valued
c(λ) ≥ 0 and all sufficiently large λ, the following holds. An unbounded sender receives Fλ and
sends w ← Enc(Fλ, r) ∈ {0, 1}^{c(λ)} to an unbounded receiver G(w, r), where r is their shared
random tape. The shared tape and the receiver's description, initial state and auxiliary oracles
are jointly independent of Fλ, and the receiver has no access to Fλ. For every such sender and
receiver, Pr_{Fλ,r}[G(Enc(Fλ, r), r) outputs tinc(λ, c(λ)) distinct elements of Fλ] ≤ εinc(λ)."

**Formalization Note.** The tape `r` ranges over any finite probability space `(R, ν)`; the
receiver's other randomness, initial state and auxiliary oracles are part of `r` (they are
independent of `F_λ`), and the sender's private randomness can be fixed to its best value, so
deterministic `Enc`, `G` given `r` lose nothing. The receiver outputs a set; "outputs `t`
distinct elements of `F_λ`" is `t ≤ |G| ∧ G ⊆ F_λ`. Only `γ(λ) → ∞` is required of `γ`: the
property refers to sufficiently large `λ` only, where `γ > 0`. -/
def IsCSI (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    (F : ∀ n, Finset (X n) → ℝ) (γ : ℕ → ℝ) : Prop :=
  Tendsto γ atTop atTop ∧
  ∀ c : ℕ → ℕ, PolyBounded c → ∃ lam0 : ℕ, ∀ lam ≥ lam0,
    ∀ (R : Type) [Fintype R] (ν : R → ℝ), IsDist ν →
    ∀ (Enc : Finset (X lam) → R → Fin (c lam) → Bool)
      (G : (Fin (c lam) → Bool) → R → Finset (X lam)),
      ∑ S : Finset (X lam), ∑ r : R, F lam S * ν r *
        (if tinc γ lam (c lam) ≤ (G (Enc S r) r).card ∧ G (Enc S r) r ⊆ S then 1 else 0)
        ≤ epsInc lam

end QMAvsQCMAH


