-- Prove2me | Definitions.Def_SecondBestBT_WellDefined
-- name    : SecondBestBT_WellDefined
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:39.450739+00:00
-- url     : https://prove2.me/theorems/d725e475-a5a2-4b04-b2b3-c522c219b424
-- title:
--   Well-defined mechanism on a type set $T$
-- statement:
--   A mechanism $(x,p_B,p_S)$ is **well defined** on the type set $T$ for the priors $F_S,F_B$ when
--
--   1. $x$, $p_B$ and $p_S$ are Borel measurable on $\mathbb R^2$;
--   2. $x(s,b)\in[0,1]$ for all $s,b\in T$;
--   3. for every report $b'\in T$ the interim payment $\int p_B(s,b')\,dF_S(s)$ exists, and for every report $s'\in T$ the interim revenue $\int p_S(s',b)\,dF_B(b)$ exists;
--   4. the expected budget surplus $\int(p_B-p_S)\,d(F_S\otimes F_B)$ and the expected gains from trade $\int (b-s)\,x(s,b)\,d(F_S\otimes F_B)$ exist.
--
--   These are the conditions under which every integral of the model is meaningful.
--
--   **Formalization Note** The paper writes these integrals without stating the conditions. Requiring them only shrinks the mechanism class, so it can only lower the second-best benchmark; the paper's own constructions (proof of Proposition 3.1, Appendix A) are measurable with integrable payments.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib
import Definitions.Def_SecondBestBT_Mechanism

open MeasureTheory

namespace SecondBestBT

/-- A mechanism is well defined on the type set `T` for the priors `μS`, `μB` when its rules are
Borel measurable, its allocation takes values in `[0, 1]` at every profile of types in `T`, and
every integral the model uses exists: the interim payments `∫ p_B(s, b') dF_S(s)` and
`∫ p_S(s', b) dF_B(b)` at every report in `T`, the expected budget surplus `∫ (p_B − p_S)`, and
the expected gains from trade `∫ (b − s) x(s, b)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 2, p.4: "x : [0, 1]² → [0, 1]", and the integrals of p.4).

**Formalization Note** The paper's integrals presuppose these conditions; stating them keeps a
non-integrable payment (whose Bochner integral would be `0`) out of the mechanism class. They
only shrink the class, so a lower bound on the second-best benchmark is not weakened. -/
def WellDefined (T : Set ℝ) (μS μB : Measure ℝ) (M : Mechanism) : Prop :=
  Measurable M.x ∧ Measurable M.pB ∧ Measurable M.pS ∧
  (∀ s ∈ T, ∀ b ∈ T, M.x (s, b) ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ b' ∈ T, Integrable (fun s => M.pB (s, b')) μS) ∧
  (∀ s' ∈ T, Integrable (fun b => M.pS (s', b)) μB) ∧
  Integrable (fun p : ℝ × ℝ => M.pB p - M.pS p) (μS.prod μB) ∧
  Integrable (fun p : ℝ × ℝ => (p.2 - p.1) * M.x p) (μS.prod μB)

end SecondBestBT


