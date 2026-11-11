-- Prove2me | Definitions.Def_NarrowDNF_Approx_DNF
-- name    : NarrowDNF_Approx_DNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:33.989402+00:00
-- url     : https://prove2.me/theorems/db3cdca8-00be-42e0-80e9-f1ace531e56b
-- title:
--   Positive-term monotone DNFs and width
-- statement:
--   A positive term is a coordinate subset $T\subseteq[n]$. A monotone DNF $g$ is a finite family of such terms, with
--   $$g(x)=\mathbf1[\exists T\in g:\ \forall i\in T,\ x_i=1],\qquad
--   \operatorname{width}(g)=\max_{T\in g}|T|.$$
--   The empty family's width is zero and its value is false. The empty term is true, so the singleton family containing it represents the true constant with width zero. Width is syntactic: adding a redundant long term may increase the family's width, but both constants retain width-zero representatives. Repeated identical terms can be removed without changing either evaluation or width. No term-count limit is built into the definition.
--
--   This is the concrete witness class in the main approximation theorem; it cannot designate an arbitrary Boolean function as narrow without an actual family of positive terms.
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Section 1, pp. 1–2 (PDF pp. 2–3)

import Definitions.Def_NarrowDNF_Approx_Probability

namespace NarrowDNF.Approx

/-- A finite family of positive terms. Repetitions do not affect its disjunction or width. -/
abbrev DNF (n : ℕ) := Finset (Finset (Fin n))

noncomputable def evalDNF {n : ℕ} (g : DNF n) (x : Cube n) : Bool := by
  classical
  exact decide (∃ T ∈ g, ∀ i ∈ T, x i = true)

/-- Maximum syntactic term cardinality; zero for the empty family. -/
def width {n : ℕ} (g : DNF n) : ℕ := g.sup Finset.card

end NarrowDNF.Approx


