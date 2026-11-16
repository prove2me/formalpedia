-- Prove2me | Definitions.Def_QiOPoQ_Supplement_ochan
-- name    : QiOPoQ_Supplement_ochan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:56:10.928284+00:00
-- url     : https://prove2.me/theorems/ba3bbd6d-6c03-47ac-94d1-1f286b8b33c0
-- title:
--   Channels and runs of oracle circuits relative to an oracle
-- statement:
--   For a classical oracle $O$, the channel of an oracle circuit relative to $O$ is
--
--   $$C^O(\rho)=\mathrm{Tr}_{\mathrm{junk}}\big[U^O_C(\rho_{\mathrm{in}}\otimes|0\rangle\langle0|_{\mathrm{anc}})U^{O\dagger}_C\big],$$
--
--   with each query gate acting by $O$, exactly as for ordinary circuits. The module also defines the probability of an output on a classical input, runs on $|0\cdots0\rangle$, and the quantum part `oqptExpect` of a QPT algorithm with oracle access.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §5.2, p.25; eq. (1), p.13

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_Supplement_OCirc

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms QAlgorithms.Complexity

variable {G : GateSet}

open Classical in
/-- The query gate `|q⟩|t⟩ ↦ |q⟩|t ⊕ O(q)⟩` on the wires `w` (query register `w 0, …, w (m−1)`,
read as the string `q`; target `w m`), the identity on the other wires. -/
noncomputable def queryMat (O : Str → Bool) {W m : ℕ} (w : Fin (m + 1) ↪ Fin W) :
    Matrix (Fin W → Bool) (Fin W → Bool) ℂ :=
  Matrix.of fun y y' =>
    if (∀ a, a ∉ Set.range w → y a = y' a) ∧ (∀ j : Fin m, y (w j.castSucc) = y' (w j.castSucc)) ∧
        y (w (Fin.last m)) = (y' (w (Fin.last m)) ^^ O (List.ofFn fun j : Fin m => y' (w j.castSucc)))
    then 1 else 0

/-- The matrix of an oracle-circuit gate relative to `O`. -/
noncomputable def ogateMat (O : Str → Bool) {W : ℕ} : OGate G W → Matrix (Fin W → Bool) (Fin W → Bool) ℂ
  | .gate g => gateMat g
  | .query _ w => queryMat O w

/-- The unitary of an oracle circuit relative to `O` (first gate applied first). -/
noncomputable def oCircUnitary (O : Str → Bool) (C : OCirc G) :
    Matrix (Fin (C.nin + C.nanc) → Bool) (Fin (C.nin + C.nanc) → Bool) ℂ :=
  C.gates.foldl (fun U g => ogateMat O g * U) 1

/-- The isometry `|x⟩ ↦ |x⟩_in ⊗ |0^{n_anc}⟩_anc`. -/
noncomputable def oInMat (C : OCirc G) : Matrix (Fin (C.nin + C.nanc) → Bool) (Fin C.nin → Bool) ℂ :=
  Matrix.of fun y x => if y = Fin.append x (fun _ : Fin C.nanc => false) then 1 else 0

open Classical in
/-- **The channel of an oracle circuit relative to `O`** (Gheorghiu, Gupte, Havlíček, Liu,
arXiv:2609.40289, sha256 fe2f9210…, eq. (1), p.13, with the query gates acting by `O`; p.25:
"circuits with O-query gates whose channels relative to O …"):
`C^O(ρ) = Tr_junk[U^O_C(ρ_in ⊗ |0⟩⟨0|_anc)U^O_C†]`, exactly as the published `QiOPoQ.chan`. -/
noncomputable def ochan (O : Str → Bool) (C : OCirc G) :
    Superop (Fin C.nin → Bool) (Fin C.out.length → Bool) :=
  fun ρ =>
    let V := oCircUnitary O C * oInMat C
    let σ := V * ρ * V.conjTranspose
    Matrix.of fun z z' => ∑ y, ∑ y',
      if (fun j => y (C.out.get j)) = z ∧ (fun j => y' (C.out.get j)) = z' ∧
          (∀ a, a ∉ C.out → y a = y' a) then σ y y' else 0

/-- `ochan` as a map from `n` to `m` qubits; the zero map when `(n_in, n_out) ≠ (n, m)`. -/
noncomputable def ochanAs (O : Str → Bool) (C : OCirc G) (n m : ℕ) :
    Superop (Fin n → Bool) (Fin m → Bool) :=
  if h : C.nin = n ∧ C.out.length = m then
    fun ρ =>
      Matrix.reindex (Equiv.arrowCongr (finCongr h.2) (Equiv.refl Bool))
        (Equiv.arrowCongr (finCongr h.2) (Equiv.refl Bool))
        (ochan O C (Matrix.reindex (Equiv.arrowCongr (finCongr h.1) (Equiv.refl Bool)).symm
          (Equiv.arrowCongr (finCongr h.1) (Equiv.refl Bool)).symm ρ))
  else fun _ => 0

/-- The probability that measuring the output register gives `z` on the basis input `|x⟩|0⟩`. -/
noncomputable def oOutProb (O : Str → Bool) (C : OCirc G) (x : Fin C.nin → Bool)
    (z : Fin C.out.length → Bool) : ℝ :=
  (ochan O C (Matrix.single x x 1) z z).re

/-- The probability that `C`, run relative to `O` on the classical input `x` (bit `i` on input
wire `i`), outputs the string `z`. -/
noncomputable def oRunProb (O : Str → Bool) (C : OCirc G) (x z : Str) : ℝ :=
  ∑ z' : Fin C.out.length → Bool,
    if List.ofFn z' = z then oOutProb O C (fun i => x.getD i.val false) z' else 0

/-- `E[g(z)]` for `z` the measured output of `C` run relative to `O` on `|0…0⟩`. -/
noncomputable def oZeroRunExpect (O : Str → Bool) (C : OCirc G) (g : Str → ℝ) : ℝ :=
  ∑ z : Fin C.out.length → Bool, oOutProb O C (fun _ => false) z * g (List.ofFn z)

/-- Run a list of oracle circuits independently on `|0…0⟩` and concatenate the outcomes. -/
noncomputable def oRunListExpect (O : Str → Bool) : List (OCirc G) → (Str → ℝ) → ℝ
  | [], g => g []
  | C :: Cs, g => oZeroRunExpect O C fun z => oRunListExpect O Cs fun rest => g (z ++ rest)

/-- The quantum part of a QPT algorithm with oracle access, as the published `QiOPoQ.qptExpect`:
`s` is a tuple of oracle-circuit descriptions; each is run relative to `O` on `|0…0⟩` and
measured; `E[g(outcomes)]`. A string that is not such a tuple gives the empty outcome. -/
noncomputable def oqptExpect (O : Str → Bool) (G : GateSet) (s : Str) (g : Str → ℝ) : ℝ :=
  match (untuple s).bind (fun l => l.mapM (decOCirc G)) with
  | some Cs => oRunListExpect O Cs g
  | none => g []

end QiOPoQ.Supplement


