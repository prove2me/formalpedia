-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_Adaptive
-- name    : PSPACEOracleSynth_Main_Supplement_Adaptive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:29:33.162978+00:00
-- url     : https://prove2.me/theorems/e6ddba76-5787-44e0-aee5-603a6235c239
-- title:
--   Adaptive resource-verification outcome trees
-- statement:
--   A finite outcome tree has a fixed number $n_{\rm inj}$ of calls along each complete history. At a node, a fresh no-input verifier targets a pure state, its acceptance flag is retained, and an outcome instrument acts on the current private register and the verified output. Each outcome selects the next node. Register sizes and instruments may depend on the history. Every call must satisfy Definition 7.3 with a common error $\varepsilon$.
--
--   The prover retains arbitrary private memory, chooses its channels from the whole transmitted history, and may process the outgoing message before its reset. The accepted run composes accepted branches, so final acceptance is the conjunction of the retained bits. The ideal run inserts exact target resources. Outcome independence means every complete ideal branch with positive probability has the same normalized state on the private register and the untouched reference. Only the initial prover memory is independent of these registers. No polynomial resource bound is imposed on this analytic tree.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 7.6 construction, pp. 40–41

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction

open QAlgorithms QAlgorithms.Complexity
open scoped Matrix ComplexOrder Kronecker
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement

/-! Lemma 7.6, pp. 40–41. A finite outcome tree. No complexity bound on this analytic
object. All paths have n calls. X may change size at every node. -/

inductive ResourceTree : ℕ → ℕ → ℕ → Type
  | done (x : ℕ) : ResourceTree 0 x x
  | call {n x out : ℕ} (V : Verifier) (χ : Bits V.o → ℂ)
      (k next rank : ℕ)
      (instrument : KAQROM.Instrument (Fin k) (Bits x × Bits V.o) (Bits next) (Fin rank))
      (children : Fin k → ResourceTree n next out) : ResourceTree (n+1) x out

/-- Every call is a verifier for its target in exactly Definition 7.3. -/
def ResourceTree.Valid (ε : ℝ) : {n x out : ℕ} → ResourceTree n x out → Prop
  | _, _, _, .done _ => True
  | _, _, _, .call V χ _ _ _ _ children =>
    V.StateVerifier χ ε ∧ ∀ v, (children v).Valid ε

/-- A prover can use the full public history and retain arbitrary private memory. The post
channel includes receiving the history and resetting/discarding the old message. A larger
finite private memory accommodates any finite run; it is never required to reset. -/
structure TreeProver (y : ℕ) where
  moves : List ℕ → (V : Verifier) → ℕ → Map (Bits V.m × Bits y) (Bits V.m × Bits y)
  channels : ∀ h V j, IsChannel (moves h V j)
  post : List ℕ → (V : Verifier) → Map (Bits V.m × Bits y) (Bits y)
  post_channel : ∀ h V, IsChannel (post h V)

def TreeProver.at {y : ℕ} (P : TreeProver y) (h : List ℕ) (V : Verifier) : ProverMoves V.m :=
  ⟨y, P.moves h V, P.channels h V⟩

/-- A single accepted resource call as a linear map on the persistent memory. -/
noncomputable def resourceCall {y : ℕ} (P : TreeProver y) (h : List ℕ) (V : Verifier) :
    Map (Bits y) (Bits V.o × (Bits V.m × Bits y)) :=
  fun τ => V.acceptedJoint (P.at h V) 0 τ (ket (fun _ => (1 : ℂ)))

/-- Attach the resource call to a possibly entangled X R M state; R is untouched. -/
noncomputable def attachResource {x r y : ℕ} (P : TreeProver y) (h : List ℕ) (V : Verifier)
    (ρ : Op (Bits x × (Bits r × Bits y))) :
    Op ((Bits x × Bits V.o) × (Bits r × (Bits V.m × Bits y))) :=
  fun a b => resourceCall P h V
    (fun u v => ρ (a.1.1,(a.2.1,u)) (b.1.1,(b.2.1,v)))
    (a.1.2,a.2.2) (b.1.2,b.2.2)

noncomputable def afterResource {x r y : ℕ} (P : TreeProver y) (h : List ℕ) (V : Verifier)
    (ρ : Op (Bits x × (Bits r × (Bits V.m × Bits y)))) :
    Op (Bits x × (Bits r × Bits y)) :=
  fun a b => P.post h V
    (fun u v => ρ (a.1,(a.2.1,u)) (b.1,(b.2.1,v))) a.2.2 b.2.2

/-- Subnormalized accepted run. Retaining each acceptance bit and accepting their conjunction
is precisely the composition of these accepted branches. -/
noncomputable def ResourceTree.run {y r : ℕ} (P : TreeProver y) :
    {n x out : ℕ} → ResourceTree n x out → List ℕ →
    Op (Bits x × (Bits r × Bits y)) → Op (Bits out × (Bits r × Bits y))
  | _, _, _, .done _, _, ρ => ρ
  | _, _, _, .call V _ k _ _ I child, h, ρ =>
    ∑ v : Fin k, (child v).run P (h ++ [v.val])
      (afterResource P (h ++ [v.val]) V
        (withRef (I.apply v) (attachResource P h V ρ)))

/-- The ideal instrument branch with the exact resource, retaining subnormalization. -/
noncomputable def exactBranch {x c z r k rank : ℕ}
    (I : KAQROM.Instrument (Fin k) (Bits x × Bits c) (Bits z) (Fin rank))
    (χ : Bits c → ℂ) (v : Fin k) (ρ : Op (Bits x × Bits r)) : Op (Bits z × Bits r) :=
  withRef (I.apply v) (fun a b => ρ (a.1.1,a.2) (b.1.1,b.2) * ket χ a.1.2 b.1.2)

/-- One subnormalized state per complete outcome sequence, including zero-probability ones. -/
noncomputable def ResourceTree.idealLeaves {r : ℕ} :
    {n x out : ℕ} → ResourceTree n x out →
    Op (Bits x × Bits r) → List (Op (Bits out × Bits r))
  | _, _, _, .done _, ρ => [ρ]
  | _, _, _, .call _ χ k _ _ I child, ρ =>
    (List.finRange k).flatMap fun v => (child v).idealLeaves (exactBranch I χ v ρ)

/-- Same final state for every ideal history with positive probability, exactly as on p. 40. -/
def ResourceTree.OutcomeIndependent {n x out r : ℕ} (T : ResourceTree n x out)
    (ψ₀ : Op (Bits x × Bits r)) (ψ' : Op (Bits out × Bits r)) : Prop :=
  ∀ ρ ∈ T.idealLeaves ψ₀, 0 < ρ.trace.re → normalized ρ = ψ'

/-- Initial memory is in product with X R, but no such product assumption is imposed later. -/
noncomputable def independentStart {x r y : ℕ} (ψ : Op (Bits x × Bits r)) (τ : Op (Bits y)) :
    Op (Bits x × (Bits r × Bits y)) :=
  fun a b => ψ (a.1,a.2.1) (b.1,b.2.1) * τ a.2.2 b.2.2

noncomputable def forgetMemory {x r y : ℕ} (ρ : Op (Bits x × (Bits r × Bits y))) :
    Op (Bits x × Bits r) := fun a b => ∑ m : Bits y, ρ (a.1,(a.2,m)) (b.1,(b.2,m))

end PSPACEOracleSynth.Main.Supplement


