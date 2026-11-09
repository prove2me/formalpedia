-- Prove2me | Definitions.Def_PfaffianRecognition_Recognition_computation_model
-- name    : PfaffianRecognition_Recognition_computation_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T04:39:24.382197+00:00
-- url     : https://prove2.me/theorems/1cfeb91d-2939-40c0-96b8-8bccc51d7bd1
-- title:
--   Encoded Pfaffian languages and polynomial bit-machine execution
-- statement:
--   Encode a graph with $N$ vertices by $N$ unary ones, a zero separator, and its $N^2$ row-major adjacency bits, using the published graph encoder. An oriented-graph encoding appends $N^2$ row-major arc bits. Let $L_G$ be exactly the valid graph encodings admitting a Pfaffian orientation, and $L_D$ exactly the valid graph/orientation encodings with Pfaffian orientation. Other strings are outside the respective languages.
--
--   For a language $L$, membership in coRP means that there exist one published finite-alphabet fair-bit machine $M$ and constants $C,k\in\mathbb N$, $C\ge1$, before all input strings. Put $B(\ell)=C(\ell+2)^k$. Every tape of $B(\ell)$ fair bits must halt within $B(\ell)$ execution steps with exactly one Boolean output. The two correctness requirements are
--   $$
--   w\in L\Longrightarrow\forall\omega,\ M(w,\omega)=1,\qquad
--   w\notin L\Longrightarrow\Pr_\omega[M(w,\omega)=0]\ge\tfrac12.
--   $$
--   Probability is the uniform count over the $2^{B(\ell)}$ tapes. This is actual execution of a fixed finite program, not an unrestricted decision function assigned a runtime value.
--
--   The deterministic orientation-reduction predicate instead chooses one finite-alphabet deterministic machine and uniform constants before all graphs. For every graph having a perfect matching, its execution must output the direction table of some orientation $D^\star$ satisfying
--   $$
--   G\text{ is Pfaffian}\iff D^\star\text{ is Pfaffian}.
--   $$
--   The runtime and correctness appear in the conclusion. This separates the mathematical predicates from the algorithms that must decide or construct them.
--
--   **Formalization Note** The common polynomial can be enlarged to dominate both time and random-bit use. The graph and oriented-graph lengths are $N+1+N^2$ and $N+1+2N^2$. Malformed, looped, asymmetric or inconsistent orientation tables can be parsed and rejected in deterministic polynomial time. All vertex counts, including zero and odd values, occur in the languages. The deterministic constructor is required only on graphs with a perfect matching, as in Lemma 3.3.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Theorem 1.1 and coRP definition, p. 3; Theorem 3.2, p. 7; Lemma 3.3 and headline proof, p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_graph_model
import Definitions.Def_CatalyticMatching_General_Encoding
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine

noncomputable section

namespace PfaffianRecognition.Recognition

/-- N² row-major direction bits, with N supplied by the graph header. -/
def orientationBits {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) : List Bool := by
  classical
  exact (CatalyticMatching.General.vertexPairs N).map fun ij => decide (D.val ij.1 ij.2)

/-- A graph header/adjacency table followed by its orientation table. -/
def orientedGraphBits {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) : List Bool :=
  CatalyticMatching.General.graphBits G ++ orientationBits D

/-- The language of all valid simple-graph encodings which are mathematically Pfaffian.
Malformed, asymmetric and looped encodings are outside the language. -/
def pfaffianLanguage (w : List Bool) : Prop :=
  ∃ (N : ℕ) (G : SimpleGraph (Fin N)),
    CatalyticMatching.General.graphBits G = w ∧ IsPfaffianGraph G

/-- The language of valid graph/orientation pairs whose orientation is Pfaffian. -/
def pfaffianOrientationLanguage (w : List Bool) : Prop :=
  ∃ (N : ℕ) (G : SimpleGraph (Fin N)) (D : Orientation G),
    orientedGraphBits D = w ∧ IsPfaffianOrientation D

/-- A single finite program and a single polynomial bound chosen before all bit strings.
The bound dominates both time and random-tape length. Every tape halts with exactly one bit;
yes instances accept on every tape and no instances reject on at least half the fair tapes.
RunsWithin is actual finite-alphabet stack-machine execution, not a claimed cost field. -/
def InCoRP (L : List Bool → Prop) : Prop :=
  ∃ M : HypergraphUnreliability.FPRAS.CoinMachine, ∃ C k : ℕ, 1 ≤ C ∧
    ∀ w : List Bool,
      let B := C * (w.length + 2) ^ k
      (∀ ω : Fin B → Bool, ∃ b : Bool,
        M.RunsWithin w (HypergraphUnreliability.FPRAS.tapeList ω) B [b]) ∧
      (L w → ∀ ω : Fin B → Bool,
        M.RunsWithin w (HypergraphUnreliability.FPRAS.tapeList ω) B [true]) ∧
      (¬ L w → (1 / 2 : ℝ) ≤ HypergraphUnreliability.FPRAS.fairProb B
        (fun ω => M.RunsWithin w (HypergraphUnreliability.FPRAS.tapeList ω) B [false]))

/-- One fixed deterministic machine constructs the stated orientation, within one uniform
polynomial bit-time bound, on every graph having a perfect matching. The orientation and its
Pfaffian equivalence are outputs in the conclusion, never correctness assumptions. -/
def HasPolyOrientationReduction : Prop :=
  ∃ M : HypergraphUnreliability.FPRAS.BitMachine, ∃ C k : ℕ, 1 ≤ C ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)),
      (∃ F : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G F) →
      ∃ D : Orientation G,
        (IsPfaffianGraph G ↔ IsPfaffianOrientation D) ∧
        Nonempty (Turing.TM2OutputsInTime M.code.tm
          ((CatalyticMatching.General.graphBits G).map M.code.inputAlphabet.symm)
          (some ((orientationBits D).map M.code.outputAlphabet.symm))
          (C * ((CatalyticMatching.General.graphBits G).length + 2) ^ k))

end PfaffianRecognition.Recognition


