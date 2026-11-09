-- Prove2me | Definitions.Def_GraphIsoTesting_FixedGraph_Padding
-- name    : GraphIsoTesting_FixedGraph_Padding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:56.761762+00:00
-- url     : https://prove2.me/theorems/c7ffe299-a377-4507-a3c2-ae6cb294f538
-- title:
--   Degree-preserving isolated padding and explicit asymptotic constants
-- statement:
--   For a graph $G$ and a natural number $r$, write $G\sqcup I_r$ for its disjoint union with $r$ isolated vertices. The oracle agrees with the core oracle on core vertices and returns null on every added vertex. For any size $N$, put
--
--   $$k=\lfloor N/13\rfloor,\qquad M=13k,\qquad r=N\bmod13<13.$$
--
--   Thus a core constructed from $m=2k$ equations has size $M$, and isolated padding gives exactly $N$ vertices without increasing degree 13. This implements the bounded-size augmentation allowed by Remark 3.7. The separate padding-distance theorem is an obligation, not an assumed field.
--
--   For $d=13$ and $K=(1+4d)^2=2809$, the constant functions record
--
--   $$\varepsilon_{\rm core}=\frac{2\beta}{13dK},\qquad
--   \varepsilon_0=\frac{\beta}{26dK},\qquad c=\frac{\delta}{13}.$$
--
--   The first formula is printed in §3.5; the latter two are explicit uniform witnesses for isolated padding. A sufficiently large size threshold absorbs the at most $4dr$ edit-distance loss. These definitions commit to one all-size realization while leaving the main theorem's positive constants existential.
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 14, §3.5 and Remark 3.7 (isolated-padding realization)

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_GraphModel

namespace GraphIsoTesting.FixedGraph

/-- Disjoint union with r isolated vertices, preserving all core edges and degrees. -/
def isolatedPadding {V : Type} (G : SimpleGraph V) (r : ℕ) :
    SimpleGraph (V ⊕ Fin r) :=
  SimpleGraph.fromRel (fun x y => ∃ u v, x = Sum.inl u ∧ y = Sum.inl v ∧ G.Adj u v)

/-- Null at each added vertex; no access to the unknown input. -/
def paddedOracle {V : Type} {d : ℕ} (oracle : IncidenceOracle V d) (r : ℕ) :
    IncidenceOracle (V ⊕ Fin r) d
  | (.inl v, p) => (oracle (v, p)).map Sum.inl
  | (.inr _, _) => none

/-- N = 13 floor(N/13) + remainder(N), with remainder below 13. -/
def coreBlocks (N : ℕ) : ℕ := N / 13
def paddingSize (N : ℕ) : ℕ := N % 13

/-- Explicit constants used to instantiate the existential all-size theorem. -/
noncomputable def coreEpsilon (β : ℝ) : ℝ := 2 * β / (13 * 13 * (1 + 4 * 13)^2)
noncomputable def paddedEpsilon (β : ℝ) : ℝ := β / (26 * 13 * (1 + 4 * 13)^2)
noncomputable def paddedSlope (δ : ℝ) : ℝ := δ / 13

end GraphIsoTesting.FixedGraph


