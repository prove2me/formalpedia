-- Prove2me | Definitions.Def_GPTIP632_Classical_Supplement_Claims
-- name    : GPTIP632_Classical_Supplement_Claims
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:17:03.782003+00:00
-- url     : https://prove2.me/theorems/6859f3de-a363-4395-8aa0-bd243ca990a1
-- title:
--   Full conclusions of the quantum and triangular companion results
-- statement:
--   This interface groups the complete source conclusions without asserting them. An induced quantum comb is the actual prover response map at every prefix: it starts with identity, is completely positive, and tracing out the last answer gives the earlier response tensored with the last question's trace. Acceptance at the fixed thresholds means value at least $2/3$ and at most $1/3$. The triangular witness sends $m^4$ copies in one prover message and consumes each once using the y measurement, with only classical gates otherwise. G1Conclusion contains the standing assumptions, classical-message equality, that witness, GMA membership, and all conditional undecidability and strict inclusions. G5Conclusion contains the standing assumptions, quantum and classical containment, theory isomorphism, both restricted-class equalities, both embedded subtheory assertions and their class identities, GMA membership, and the conditional separation. G7Conclusion contains the computable coordinate, both computable cone descriptions, units and gates, computable forward and inverse isomorphisms, both GMA memberships, PSPACE nonmembership, decidability in space $2^{c(\lfloor\log_2m\rfloor+1)^2}$ for one constant and one total OTM, both standing assumptions, quantum and classical containment, both strict separations and all restricted-class equalities. These predicates always refer to the concretely specified pretheories and never accept an arbitrary theory in their place.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.14, 17–19, 22–23, 28, 32–35 (PDF pp.16, 19–21, 24–25, 30, 34–37), Examples B.3, B.5, B.17–B.23, Definitions D.3–D.4, F.1, §G

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Triangular
import Definitions.Def_GPTIP632_Classical_IP

set_option autoImplicit false

noncomputable section
namespace GPTIP632.Classical.Supplement
open Matrix QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
attribute [local instance] _root_.Classical.propDecidable

/-- Definition F.1 for the actual induced response maps, including every prefix. -/
def InducedQuantumComb {G : Theory} (E : QEmb G) (V : VData G) (x : Str)
    (P : Prover V x) : Prop :=
  comb P 0 [] [] = 1 ∧
  (∀ j, j ≤ V.R x → IsCPker E.wire (catMsgs (V.Q x) j) (catMsgs (V.A x) j) (comb P j)) ∧
  ∀ j, j < V.R x →
    ∀ ka ∈ G.C.coords (catMsgs (V.A x) j), ∀ kq ∈ G.C.coords (catMsgs (V.Q x) j),
    ∀ kin ∈ G.C.coords (V.Q x j),
      (∑ kout ∈ G.C.coords (V.A x j), G.C.rawUnit kout * comb P (j + 1) (ka ++ kout) (kq ++ kin)) =
        comb P j ka kq * G.C.rawUnit kin

/-- Completeness and soundness at the fixed source thresholds. -/
def DecidesByValue {G : Theory} (V : VData G) (L : KTUnitary.Synth.PromiseProblem) : Prop :=
  (∀ x ∈ L.1, (2 : ℝ) / 3 ≤ V.val x) ∧ (∀ x ∈ L.2, V.val x ≤ 1 / 3)

/-- The protocol shape in G.1(ii). Only the y measurement acts on incoming triangular wires;
classical gates may process the recorded results. Each triangular wire is consumed once. -/
def TriangularProtocol (v : Set.Ioo (0 : ℝ) 1) (h : (gvPre v).Ok)
    (V : VData ((gvPre v).toTheory h)) : Prop :=
  (∀ x, V.R x = 1) ∧
  (∀ x i, V.Q x i = []) ∧
  (∀ x, V.A x 0 = List.replicate (x.length ^ 4) GvElem.wtri) ∧
  (∀ x z, V.next x 0 z = .halt) ∧
  ∀ x, 0 < x.length → ∀ ws q a b w ss,
    V.stageSteps x 1 b (VData.hist ws q a 1) w = some ss →
      ss.countP (fun st => match st with | .apply (.inr .measY) _ => true | _ => false) = x.length ^ 4 ∧
      ∀ st ∈ ss, match st with
        | .halt => True
        | .apply (.inl _) _ => True
        | .apply (.inr .measY) _ => True
        | _ => False

/-- All clauses of G.1, for the concretely specified pretheory, with its theory axioms supplied
as an existential conclusion in the theorem rather than as an assumption. -/
def G1Conclusion (v : Set.Ioo (0 : ℝ) 1) (h : (gvPre v).Ok) : Prop :=
  let G := (gvPre v).toTheory h
  G.Standing ∧ GIPcl G = PromisePSPACE O₀ ∧
  (∃ V : VData G, V.IsVerifier ∧ TriangularProtocol v h V ∧ DecidesByValue V (Lv v)) ∧
  Lv v ∈ GMA G ∧
  (¬ DetParamSVP.IsComputableReal v →
    ¬ DecidablePP (Lv v) ∧
    (∃ L ∈ GMA G, ¬ DecidablePP L) ∧
    PromisePSPACE O₀ ⊂ GIP G ∧ GIPcl G ⊂ GIP G)

/-- All clauses of G.5, including the subtheory assertions and their two class identities. -/
def G5Conclusion (v : Set.Ioo (0 : ℝ) 1)
    (hQ : (qcPre []).Ok) (hC : (clPre []).Ok) (h3 : (qcPre [2]).Ok)
    (h : (gqvPre v).Ok) (E : QEmb ((gqvPre v).toTheory h)) : Prop :=
  let G := (gqvPre v).toTheory h
  G.Standing ∧ G.T3 ∧
  Nonempty (TheoryIso G ((qcPre [2]).toTheory h3)) ∧
  GIPcl G = PromisePSPACE O₀ ∧ GIPqm G E hQ = PromisePSPACE O₀ ∧
  Nonempty (Subtheory (qc0 hQ) G) ∧
  GIP (qc0 hQ) = QIP hQ ∧ QIP hQ = PromisePSPACE O₀ ∧
  Nonempty (Subtheory ((clPre []).toTheory hC) G) ∧
  GIP ((clPre []).toTheory hC) = IP ∧ IP = PromisePSPACE O₀ ∧
  Lv v ∈ GMA G ∧
  (¬ DetParamSVP.IsComputableReal v →
    (∃ L ∈ GIP G, ¬ DecidablePP L) ∧ PromisePSPACE O₀ ⊂ GIP G)

/-- The decidability and full space bound of G.7(iv). Unary logarithm conventions are avoided
by bounding every positive and zero input length with `log₂ m + 1`. -/
def QuasipolySpaceDecidable (L : KTUnitary.Synth.PromiseProblem) : Prop :=
  DecidablePP L ∧ ∃ (c : ℕ) (M : OTM), ∀ x : Str, ∃ t : ℕ,
    M.result O₀ x t ≠ none ∧
    M.space O₀ x t ≤ 2 ^ (c * (Nat.log 2 x.length + 1) ^ 2) ∧
    (x ∈ L.1 → M.result O₀ x t = some true) ∧
    (x ∈ L.2 → M.result O₀ x t = some false)

/-- The computable presentation, class memberships, nonmembership and all consequences of G.7.
The coordinate and the two theories are fixed by the source constructions. -/
def G7Conclusion (T : Set ℕ) (hv : vT T ∈ Set.Ioo (0 : ℝ) 1)
    (hQ : (qcPre []).Ok) (hC3 : (clPre [2]).Ok) (hQ3 : (qcPre [2]).Ok)
    (h : (gvPre ⟨vT T, hv⟩).Ok) (h' : (gqvPre ⟨vT T, hv⟩).Ok)
    (E : QEmb ((gqvPre ⟨vT T, hv⟩).toTheory h')) : Prop :=
  let G := (gvPre ⟨vT T, hv⟩).toTheory h
  let GQ := (gqvPre ⟨vT T, hv⟩).toTheory h'
  DetParamSVP.IsComputableReal (vT T) ∧
  LinearComputableCones G ∧ PSDComputableCones GQ ∧
  ComputableUnitsGates G ∧ ComputableUnitsGates GQ ∧
  (∃ φ : TheoryIso G ((clPre [2]).toTheory hC3), φ.Computable) ∧
  (∃ φ : TheoryIso GQ ((qcPre [2]).toTheory hQ3), φ.Computable) ∧
  Lv (vT T) ∈ GMA G ∧ Lv (vT T) ∈ GMA GQ ∧
  Lv (vT T) ∉ PromisePSPACE O₀ ∧ QuasipolySpaceDecidable (Lv (vT T)) ∧
  G.Standing ∧ GQ.Standing ∧ GQ.T3 ∧
  PromisePSPACE O₀ ⊂ GIP G ∧ PromisePSPACE O₀ ⊂ GIP GQ ∧
  GIPcl G = PromisePSPACE O₀ ∧ GIPcl GQ = PromisePSPACE O₀ ∧
  GIPqm GQ E hQ = PromisePSPACE O₀

end GPTIP632.Classical.Supplement
end


