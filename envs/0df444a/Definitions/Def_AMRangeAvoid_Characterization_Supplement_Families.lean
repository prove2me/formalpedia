-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Supplement_Families
-- name    : AMRangeAvoid_Characterization_Supplement_Families
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:24:47.616899+00:00
-- url     : https://prove2.me/theorems/222d90b5-3d45-41c2-ba1d-e0ee7d389b04
-- title:
--   Literal composition of decision reductions with the SSLB Avoid producer
-- statement:
--   A particular deterministic decision transducer is a fixed polynomial-time map preserving both promised sides. Given such a graph- or lattice-to-SSLB map $h$ and an SSLB-to-Avoid producer $f$, the natural family is their literal composition
--
--   $$f_{\mathrm{natural}}(x)=f(h(x)).$$
--
--   Theorem 1.11 constructs these maps and establishes their correctness in its conclusion. The source's unchanged SSLB verifier is reused from the published definition. Neither an algorithm solving the source decision problem nor a family with an assumed complexity implication is included as input data.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), §5, printed pp.24–25 (PDF pp.26–27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Graphs
import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Lattices
import Definitions.Def_AMRangeAvoid_Characterization_Protocol

namespace AMRangeAvoid.Characterization.Supplement

/-- A particular decision transducer, with the same two promises as the base
existential PromiseReduces. Correctness is a property to prove, not machine data. -/
def DecisionMap (A B : PromiseProblem) (h : Bits → Bits) : Prop :=
  PolyTime h ∧ (∀ x ∈ A.yes, h x ∈ B.yes) ∧ (∀ x ∈ A.no, h x ∈ B.no)

/-- The actual composition in §5: a graph/lattice-to-SSLB transducer followed
by the SSLB-to-Avoid circuit producer. Theorem 1.11 constructs BOTH transducers
and proves their correctness as part of its conclusion. No arbitrary family is
assumed to satisfy the desired complexity implication. -/
def composedFamily (toSSLB producer : Bits → Bits) : Bits → Bits :=
  fun x => producer (toSSLB x)

end AMRangeAvoid.Characterization.Supplement


