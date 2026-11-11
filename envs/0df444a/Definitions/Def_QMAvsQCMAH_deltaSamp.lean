-- Prove2me | Definitions.Def_QMAvsQCMAH_deltaSamp
-- name    : QMAvsQCMAH_deltaSamp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:28.079187+00:00
-- url     : https://prove2.me/theorems/d014fa8c-5915-4e70-ace2-387b6ab25ab0
-- title:
--   The simulation parameters $c,\ Q_{\mathrm{sim}},\ m,\ \delta_{\mathrm{samp}}$
-- statement:
--   For integers $\ell,t,L\ge1$, a finite set $\mathcal Z$ of auxiliary inputs, a domain $\mathcal X$, $Q$ queries and $0<\eta<1$:
--   $$c=\ell+\lceil\log_2|\mathcal Z|\rceil,\quad Q_{\mathrm{sim}}=t^2L,\quad m=c+t(\lceil\log_2Q_{\mathrm{sim}}\rceil+1),\quad\delta_{\mathrm{samp}}=2^c(|\mathcal X|+1)^t\,t\,e^{-\eta^2L/(16Q^2)}.$$
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Theorem 5, p.31, Equation (22)

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

/-- The parameter `c = ℓ + ⌈log₂ |Z|⌉` of Equation (22) (witness length plus auxiliary-input
length). -/
def cParam (ℓ Zc : ℕ) : ℕ := ℓ + Nat.clog 2 Zc

/-- The simulator's query budget `Q_sim = t²L` of Equation (22). -/
def qSim (t L : ℕ) : ℕ := t ^ 2 * L

/-- The message length `m = c + t(⌈log₂ Q_sim⌉ + 1)` of Equation (22). -/
def mSim (ℓ Zc t L : ℕ) : ℕ := cParam ℓ Zc + t * (Nat.clog 2 (qSim t L) + 1)

/-- The sampling error `δ_samp = 2^c (|X| + 1)^t t e^{−η²L/(16Q²)}` of Equation (22).

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Theorem 5, p.31 (PDF p.34), Equation (22): "For integers t, L ≥ 1 and 0 < η < 1, put
c = ℓ + ⌈log2 |Z|⌉, Qsim = t²L, m = c + t(⌈log2 Qsim⌉ + 1),
δsamp = 2^c (|X| + 1)^t t e^{−η²L/(16Q²)}."

**Formalization Note.** `⌈log₂ n⌉` is `Nat.clog 2 n`. -/
noncomputable def deltaSamp (ℓ Zc Xc t L Q : ℕ) (η : ℝ) : ℝ :=
  (2 : ℝ) ^ cParam ℓ Zc * ((Xc : ℝ) + 1) ^ t * t *
    Real.exp (-(η ^ 2 * L / (16 * (Q : ℝ) ^ 2)))

end QMAvsQCMAH


