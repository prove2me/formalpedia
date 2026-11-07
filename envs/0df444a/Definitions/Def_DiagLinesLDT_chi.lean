-- Prove2me | Definitions.Def_DiagLinesLDT_chi
-- name    : DiagLinesLDT_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:04.208433+00:00
-- url     : https://prove2.me/theorems/fba47098-d4e6-4fd8-bdf1-07fb50f85767
-- title:
--   The additive character $\chi(t)=\exp(2\pi i\operatorname{Tr}_{q/p}(t)/p)$
-- statement:
--   Let $\mathbb F_q$ have characteristic $p$, and let $\operatorname{Tr}_{q/p}:\mathbb F_q\to\mathbb F_p$ be the field trace. The additive character of the construction is
--
--   $$\chi(t):=\exp\Big(\frac{2\pi i}{p}\operatorname{Tr}_{q/p}(t)\Big).$$
--
--   It is the only source of phases in the construction. For $q=p$ it is $\omega^t$ with $\omega=e^{2\pi i/q}$, and for $p=2$ it is $(-1)^{\operatorname{Tr}_{q/2}(t)}$.
--
--   **Formalization Note** One definition covers §§4, 7.1 and 7.2. The representative of $\operatorname{Tr}_{q/p}(t)$ in $\{0,\dots,p-1\}$ is used in the exponent.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §7.1, p.21, and §7.2, p.23

import Mathlib

namespace DiagLinesLDT

/-- The field trace `Tr_{q/p} : 𝔽_q → 𝔽_p` with `p` the characteristic of `F`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §7.1, p.21. -/
noncomputable def fieldTrace (F : Type*) [Field F] [Fintype F] (t : F) : ZMod (ringChar F) :=
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  Algebra.trace (ZMod (ringChar F)) F t

/-- The additive character `χ(t) = exp(2π i Tr_{q/p}(t) / p)`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §7.1, p.21, and §7.2,
p.23.

**Formalization Note** One definition covers all characteristics. At `q = p` the trace is the identity
and `χ(t) = ω^t` (§4); at `p = 2` it is `(-1)^{Tr(t)}` (§7.2). Both, additivity and nontriviality are
checked in `Solutions/verification/DiagLinesLDT_sanity.lean`. -/
noncomputable def chi (F : Type*) [Field F] [Fintype F] (t : F) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((fieldTrace F t).val : ℂ) / (ringChar F : ℂ))

end DiagLinesLDT


