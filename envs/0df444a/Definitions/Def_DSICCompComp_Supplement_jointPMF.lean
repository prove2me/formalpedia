-- Prove2me | Definitions.Def_DSICCompComp_Supplement_jointPMF
-- name    : DSICCompComp_Supplement_jointPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:23:39.662181+00:00
-- url     : https://prove2.me/theorems/c5f2a390-7dc8-4e5e-a0d2-441f4c620227
-- title:
--   Joint PMF $f(v) = \prod_i f_i(v_i)$
-- statement:
--   In the finite-support setting, the joint probability mass function of the value profile $v = (v_1, \dots, v_n) \in \mathrm{supp}(D) = \times_i \mathrm{supp}(D_i)$ is
--
--   $$
--   f(v) \;=\; \prod_{i=1}^n f_i(v_i).
--   $$
--
--   It is positive on $\mathrm{supp}(D)$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.34 (pdf p.35)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_FiniteSetting

namespace DSICCompComp

namespace Supplement

/-- The joint PMF `f` of the value profile `v = (v_1, …, v_n) ∈ supp(D) = ×_i supp(D_i)`
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.34 (pdf p.35)): `f(v) = ∏_i f_i(v_i)`, since `D = ×_i D_i`.

**Formalization Note** A profile in `supp(D)` is a dependent function `v : (i : Fin n) → S i`. -/
def jointPMF {n m : ℕ} (E : FiniteSetting n m) (v : (i : Fin n) → E.S i) : ℝ :=
  ∏ i, E.f i (v i)

end Supplement

end DSICCompComp


