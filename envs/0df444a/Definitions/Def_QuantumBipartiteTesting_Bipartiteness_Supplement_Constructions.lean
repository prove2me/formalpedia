-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Constructions
-- name    : QuantumBipartiteTesting_Bipartiteness_Supplement_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:11:31.892991+00:00
-- url     : https://prove2.me/theorems/0006b04e-bd1d-4d28-b88d-97b45e592ffd
-- title:
--   Colored cuts, replacement graphs, and distinct-edge subdivisions
-- statement:
--   A colored edge retains its color as part of its identity, so distinct colors can give parallel edges. Crossing counts include this multiplicity. A cubic cloud is an actual simple graph with degree exactly three; the cloud predicate additionally requires its all-cuts edge expansion bound.
--
--   For a fixed relabeling of $[n]\times[c]$ and a fixed cloud $J$, the replacement graph contains a copy of $J$ at each intermediate vertex and one external edge $\{(u,j),(v,j)\}$ per color-$j$ edge $uv$. Its oracle uses the three internal neighbor slots, followed by the optional external neighbor. Its simplicity, degree bound and packed representation are theorem conclusions, not fields of this definition.
--
--   Support and probability are computed using the published finite feasible sampling law. The explicit cut-failure sum is $\sum_{u=1}^{\lfloor n/2\rfloor}\binom nu e^{-cu/80}$. Subdivision removes a set $T$ of distinct original edges and replaces each by two edges through its own fresh vertex. Old vertices precede the fresh vertices; an arbitrary bijection labels the latter. The definitions also record $c(N)=2\lceil200\ln N\rceil$, $n(N)=\lfloor N/c(N)\rfloor$ and the remainder, for the final-size convention.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §4.1–4.2, printed = PDF pp.22–25; §4.3 pp.26–27; Appendices A.7–A.10 pp.37–40

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Expansion
import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Sampling

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def ColoredCrossing {n c : ℕ} (H : Finset (ColoredEdge n c)) (U : Finset (Fin n)) :=
  H.filter fun e => (e.1 ∈ U ∧ e.2.1 ∉ U) ∨ (e.2.1 ∈ U ∧ e.1 ∉ U)

def ColoredExpansion {n c : ℕ} (β : ℝ) (H : Finset (ColoredEdge n c)) : Prop :=
  ∀ U : Finset (Fin n), β * c * min (U.card : ℝ) (n - (U.card : ℝ)) ≤
    (ColoredCrossing H U).card

def Cloud {c : ℕ} (h₀ : ℝ) (J : Finset (Edge c)) : Prop :=
  IsGraph J ∧ (∀ u, (Neighbors J u).card = 3) ∧ EdgeExpander h₀ J

def Cubic {c : ℕ} (J : Finset (Edge c)) : Prop :=
  IsGraph J ∧ ∀ u, (Neighbors J u).card = 3

def UnsignedResponse {n c : ℕ} (H : Finset (ColoredEdge n c))
    (a : Fin n × Fin c) : Option (Fin n) :=
  (SignedResponse H (fun _ => false) a).map Prod.fst

/-- e is a fixed relabeling of the product vertices, independent of H. -/
def Replacement {n c : ℕ} (e : Fin (n*c) ≃ Fin n × Fin c)
    (J : Finset (Edge c)) (H : Finset (ColoredEdge n c)) : Finset (Edge (n*c)) :=
  univ.filter fun xy => xy.1 < xy.2 ∧
    (( (e xy.1).1 = (e xy.2).1 ∧ (e xy.2).2 ∈ Neighbors J (e xy.1).2) ∨
     ((e xy.1).2 = (e xy.2).2 ∧
      (( (e xy.1).1, (e xy.2).1, (e xy.1).2) ∈ H ∨
       ( (e xy.2).1, (e xy.1).1, (e xy.1).2) ∈ H)))

/-- Three internal slots followed by the optional external color edge. -/
def ReplacementOracle {n c : ℕ} (e : Fin (n*c) ≃ Fin n × Fin c)
    (P : Fin c × Fin 3 → Option (Fin c)) (H : Finset (ColoredEdge n c))
    (a : Fin (n*c) × Fin 4) : Option (Fin (n*c)) :=
  let uj := e a.1
  if hi : a.2.val < 3 then
    (P (uj.2, ⟨a.2.val, hi⟩)).map fun j => e.symm (uj.1,j)
  else (UnsignedResponse H uj).map fun v => e.symm (v,uj.2)

/-- Support of the actual finite feasible law, rather than a property certificate. -/
def InSupport (n M l c : ℕ) (H : Finset (ColoredEdge n c)) : Prop :=
  0 < FeasibleBase n M l (fun F => if F = H then 1 else 0)

def FeasibleProb (n M l c : ℕ) (P : Finset (ColoredEdge n c) → Prop) : ℝ :=
  FeasibleBase n M l (fun H => if P H then 1 else 0)

def CutFailureBound (n c : ℕ) : ℝ :=
  ∑ u ∈ Icc 1 (n/2), (n.choose u : ℝ) * Real.exp (-(c : ℝ) * u / 80)

/-- Old vertices stay first; the selected original edges index distinct fresh vertices. -/
def Subdivision {m : ℕ} (G T : Finset (Edge m))
    (idx : {x // x ∈ T} ≃ Fin T.card) : Finset (Edge (m + T.card)) :=
  let old : Fin m → Fin (m + T.card) := Fin.castAdd T.card
  let fresh : {x // x ∈ T} → Fin (m + T.card) := fun x => Fin.natAdd m (idx x)
  ((G \ T).image fun x => (old x.1, old x.2)) ∪
    (T.attach.biUnion fun x =>
      {(min (old x.val.1) (fresh x), max (old x.val.1) (fresh x)),
       (min (old x.val.2) (fresh x), max (old x.val.2) (fresh x))})

/-- Final-size-driven choice; used to avoid gaps between products n*c. -/
def FinalColors (N : ℕ) : ℕ := 2 * ⌈200 * Real.log N⌉₊
def IntermediateSize (N : ℕ) : ℕ := N / FinalColors N
def SizeRemainder (N : ℕ) : ℕ := N - IntermediateSize N * FinalColors N

end
end QuantumBipartiteTesting.Bipartiteness.Supplement


