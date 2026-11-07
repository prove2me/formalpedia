-- Prove2me | Definitions.Def_KTUnitary_Synth_BQUPSPACEplain
-- name    : KTUnitary_Synth_BQUPSPACEplain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:27.694204+00:00
-- url     : https://prove2.me/theorems/5ece7b5b-fb65-4f06-ada9-351d626fabc8
-- title:
--   The class $\mathsf{BQUPSPACE}^L$ of Definition 4.6
-- statement:
--   For a language $L$: as $\mathsf{BQUPSPACE}^{\mathcal O}$ with $\mathcal O$ the unitary embedding of $L$, but every circuit uses only the plain oracle gates $U_m|x,b\rangle=|x,b\oplus L(x)\rangle$ of Definition 4.4 (no conjugated, adjoint, transposed or controlled oracle gates).
--
--   This is the class in Proposition 4.8, $\mathsf{BQPSPACE}^L=\mathsf{BQUPSPACE}^L=\mathsf{PSPACE}^L$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6 and Proposition 4.8, p. 15

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_ancPad
import Definitions.Def_KTUnitary_Synth_measProb
import Definitions.Def_KTUnitary_Synth_PromiseProblem
import Definitions.Def_KTUnitary_Synth_SpaceUniform
import Definitions.Def_KTUnitary_Synth_emb

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `BQUPSPACE^L` of Definition 4.6, with the oracle gates of Definition 4.4**
(Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6 and Proposition 4.8, p. 15): "`BQUPSPACE^L` is defined identically [to
`BQPSPACE^L`], except with a space-uniform family of unitary quantum circuits", where an `L`-oracle
circuit has explicit gates and oracle gates `U_m |x, b⟩ = |x, b ⊕ L(x)⟩` only (Definition 4.4).

Here: as `BQUPSPACE (emb L)`, with every circuit `Plain` (no conjugated, adjoint, transposed or
controlled oracle gates).

**Formalization Note** Proposition 4.8 is about this class. The class with all eight gate kinds,
`BQUPSPACE (emb L)` (footnote 7, p. 24), is the one of Theorem 6.17. The output wire `o n` is printed
with the circuit, as in `BQUPSPACE`. -/
def BQUPSPACEplain (L : Oracle) : Set PromiseProblem :=
  {pr | ∃ (f : Str → ℝ) (C : ℕ → UCircuit) (o : (n : ℕ) → Fin (C n).N) (p : Polynomial ℕ),
    HasFPTEAS f ∧
    SpaceUniform (fun n : ℕ => tup [unary n]) (fun n => tup [(C n).code, Nat.bits (o n)])
      (fun n => (C n).gateCodes) ∧
    ∀ n : ℕ, (C n).Plain ∧ (C n).Valid f ∧ ∃ h : n ≤ (C n).N, (C n).N ≤ n + p.eval n ∧
      ∀ x : Bits n,
        (List.ofFn x ∈ pr.1 → (2 / 3 : ℝ) ≤
          measProb (((C n).unitary f (emb L)).mulVec (ancPad h (Pi.single x 1))) (fun z => z (o n) = true)) ∧
        (List.ofFn x ∈ pr.2 →
          measProb (((C n).unitary f (emb L)).mulVec (ancPad h (Pi.single x 1))) (fun z => z (o n) = true)
            ≤ 1 / 3)}

end KTUnitary.Synth


