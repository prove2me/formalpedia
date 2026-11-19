-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol
-- name    : DecrAlmostLinearSSSP_NonemptyCutProtocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-19T04:13:29.41673+00:00
-- url     : https://prove2.me/theorems/5bd3f8be-3207-4a03-9c27-2e68bd29e338
-- title:
--   Dynamic cut protocol on nonempty vertex domains
-- statement:
--   This is the dynamic cut interface used by the decremental shortest-path algorithm, interpreted only on nonempty vertex domains.
--
--   For each number of vertices $n>0$ and number of edge identifiers $k$, one finite deterministic arithmetic-RAM program has a semantic state view
--
--   $$\mathcal V_{n,k}:\mathrm{Machine}\longrightarrow\mathrm{CutState}(n,k).$$
--
--   The state contains the physical graph, vertex potentials, detector baselines and the most recently returned cut. Legal operations and correctness use the physical updates, cut ratios, potential shifts, stored-array reports and query outputs of Lemma 3.2. The execution relation admits only actual terminating runs of this program. Correctness, totality, the report bound and amortized work are conclusions of its implementation predicate.
--
--   This interface retains the source's nonempty input domain. Requiring a state view for $n=0,k=1$ would demand a graph endpoint in the empty vertex set, even though that pair is never an admitted graph instance.
--
--   **Formalization Note** The interpretation function takes an erased proof that $n>0$. Its `view` wrapper uses a `NeZero n` instance to supply that proof. No extra machine input or runtime instruction is granted by the proof argument.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p. 9, Lemma 3.2 and §3.2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. Nonempty vertex-domain interpretation of the stated physical graph interface.

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_CutProtocol

set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- A semantic view is needed only on nonempty vertex domains. The proof is erased and
is never an extra machine input. The finite program remains uniform in all graph sizes. -/
structure Implementation where
  program : Program
  interpret : (n k : ℕ) → 0 < n → Machine → CutState n k

noncomputable def Implementation.view (impl : Implementation) (n k : ℕ) [NeZero n] (c : Machine) : CutState n k :=
  impl.interpret n k (Nat.pos_of_ne_zero (NeZero.ne n)) c

/-- The source operation domain and all physical, potential, detector and ratio
conclusions are retained verbatim. Only the interpretation domain has changed. -/
abbrev ValidRequest {n k : ℕ} (s : CutState n k) (op : CutOp n k) : Prop := CutOp.Valid s op
noncomputable abbrev Transition {n k : ℕ} (K ξ : ℝ) (s : CutState n k) (op : CutOp n k)
    (c : Machine) (t : CutState n k) : Prop := CutTransition K ξ s op c t

/-- Executions have no correctness certificate among their constructor inputs. -/
inductive Run (impl : Implementation) (n k m exponent : ℕ) [NeZero n] (first : Machine) :
    List (CutOp n k) → List Machine → Prop
  | start : Run impl n k m exponent first [] [first]
  | next {ops : List (CutOp n k)} {cs : List Machine} {c d : Machine}
      (hr : Run impl n k m exponent first ops cs) (hl : cs.getLast? = some c)
      (op : CutOp n k) (hv : ValidRequest (impl.view n k c) op)
      (hb : (applyPhysical (impl.view n k c).physical op).Valid m exponent)
      (he : Ends impl.program (cutRequest impl.program c op) d) :
      Run impl n k m exponent first (ops ++ [op]) (cs ++ [d])

def Implements (impl : Implementation) (m exponent : ℕ) (K h Γ init ξ : ℝ) : Prop :=
  ∀ n k [NeZero n] (graph : Physical n k) (capacityBound : ℝ), graph.Valid m exponent →
    0 < capacityBound → capacityBound ≤ (max 2 m : ℝ) ^ exponent →
    (∀ e ∈ graph.active, graph.u e ≤ capacityBound) →
    ∃ first, Ends impl.program (cutInitial impl.program graph m ξ capacityBound) first ∧
      (impl.view n k first).physical = graph ∧ (impl.view n k first).y = 0 ∧
      (impl.view n k first).baseline = 0 ∧ (impl.view n k first).hasCut = false ∧ (first.work : ℝ) ≤ init ∧
      ∀ ops cs, Run impl n k m exponent first ops cs →
        (∀ c, cs.getLast? = some c → ∀ op, ValidRequest (impl.view n k c) op →
          (applyPhysical (impl.view n k c).physical op).Valid m exponent →
          ∃ d, Ends impl.program (cutRequest impl.program c op) d ∧
            Transition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (∀ (j : ℕ) c d op, cs[j]? = some c → cs[j+1]? = some d → ops[j]? = some op →
          Transition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (let T := (ops.filter (fun op => match op with | .toggle _ => true | _ => false)).length
         let R := ((cs.drop 1).map reportCount).sum
         (R : ℝ) ≤ Γ * T / ξ ∧
           ∀ last, cs.getLast? = some last →
             (last.work + 6 * ops.length : ℕ) ≤ init + h * (ops.length + R))

end DecrAlmostLinearSSSP.Decremental.NonemptyCut


