-- Prove2me | Definitions.Def_KTUnitary_Synth_UCircuit
-- name    : KTUnitary_Synth_UCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:30:17.507714+00:00
-- url     : https://prove2.me/theorems/f19c7a61-9d63-4e37-8c29-8b2df524af0f
-- title:
--   Oracle unitary quantum circuit with FPTEAS gates
-- statement:
--   An **$\mathcal O$-oracle unitary quantum circuit** on $N$ qubits is a finite sequence of gates, each of which is
--   1. an explicitly specified $k$-qubit gate on $k$ distinct wires, whose $2^k\times2^k$ matrix has entries $f(x)+f(y)\,i$ given by pairs of strings $(x,y)$ for the circuit family's FPTEAS encoding $f$; or
--   2. an oracle gate $O_m$, $O_m^*$, $O_m^\dagger$ or $O_m^T$ on $m$ distinct wires, or its controlled version on $m+1$ wires, specified only by its label and wires.
--
--   The circuit's **description** lists $N$ and, for each gate, its label, its wires in binary and (for an explicit gate) all its entry strings. The **unitary** of the circuit is the product of the gate matrices, the first gate rightmost, with explicit global phase. The circuit is **valid** for $f$ if every explicit gate's matrix is unitary, and **plain** if it uses only uncontrolled $O_m$ oracle gates (Definition 4.4's $L$-oracle circuits).
--
--   Exact FPTEAS entries let a circuit contain rotations by rational multiples of $2\pi$ or Fourier transforms without compiling them; a gate is still a short string, so an exponentially large unitary cannot be written as one gate within the uniformity bounds.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2, 4.3 and 5.5, pp. 14, 17

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_ULang
import Definitions.Def_KTUnitary_Synth_OKind
import Definitions.Def_KTUnitary_Synth_embedGate
import Definitions.Def_KTUnitary_Synth_ctrlMat
import Definitions.Def_KTUnitary_Synth_allBits

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **A gate of an oracle unitary quantum circuit on `N` qubits** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2, 4.3 and
5.5, pp. 14 and 17).

* `expl k w ent`: an explicitly specified `k`-qubit gate on the distinct wires `w`; the entry in
  row `i`, column `j` of its `2^k × 2^k` matrix is described by the pair of strings `ent i j = (x, y)`,
  denoting the complex number `f(x) + f(y)·i` for the circuit's FPTEAS encoding `f` ("each complex
  entry `a + bi` … is described by a pair `x, y ∈ {0,1}*` for which `f(x) = a` and `f(y) = b`").
* `orac κ m w`: the oracle gate `κ(O_m)` (one of `O_m, O_m^*, O_m^†, O_m^T`) on the `m` distinct
  wires `w`.
* `corac κ m w`: the controlled oracle gate `cκ(O_m)` on the `m + 1` distinct wires `w`, with the
  control on `w 0`.

"These oracle gates are specified only by the label and the qubits acted upon" (Definition 5.5). -/
inductive UGate (N : ℕ)
  | expl (k : ℕ) (w : Fin k ↪ Fin N) (ent : Bits k → Bits k → Str × Str)
  | orac (κ : OKind) (m : ℕ) (w : Fin m ↪ Fin N)
  | corac (κ : OKind) (m : ℕ) (w : Fin (m + 1) ↪ Fin N)

/-- The matrix described by the entry strings `ent` under the encoding `f`:
entry `(i, j)` is `f(x) + f(y)·i` for `ent i j = (x, y)`. -/
noncomputable def decodeU (f : Str → ℝ) {k : ℕ} (ent : Bits k → Bits k → Str × Str) :
    Matrix (Bits k) (Bits k) ℂ :=
  Matrix.of fun i j => (f (ent i j).1 : ℂ) + (f (ent i j).2 : ℂ) * Complex.I

namespace UGate

/-- The description of a gate: a tag, the size, the wire labels in binary and, for an explicit
gate, the `2 · 4^k` entry strings in the order of `allBits k`. For an oracle gate, only the label
(kind, control, index `m`) and the wires. -/
def code {N : ℕ} : UGate N → Str
  | .expl k w ent => tup ([false, false] :: Nat.bits k :: (List.ofFn fun q => Nat.bits (w q)) ++
      ((allBits k).flatMap fun i => (allBits k).flatMap fun j => [(ent i j).1, (ent i j).2]))
  | .orac κ m w => tup ([false, true] :: κ.code :: Nat.bits m :: List.ofFn fun q => Nat.bits (w q))
  | .corac κ m w => tup ([true, false] :: κ.code :: Nat.bits m :: List.ofFn fun q => Nat.bits (w q))

/-- The `2^N × 2^N` matrix of a gate, for the encoding `f` and the unitary oracle `𝒪`. -/
noncomputable def mat (f : Str → ℝ) (O : ULang) {N : ℕ} : UGate N → Matrix (Bits N) (Bits N) ℂ
  | .expl _ w ent => embedGate w (decodeU f ent)
  | .orac κ m w => embedGate w (κ.act (O m : Matrix (Bits m) (Bits m) ℂ))
  | .corac κ m w => embedGate w (ctrlMat (κ.act (O m : Matrix (Bits m) (Bits m) ℂ)))

/-- An explicit gate is valid for `f` if the matrix it describes is unitary (Definition 4.3: "each
gate is a unitary superoperator `ρ ↦ U ρ U^†` specified by the `2^k × 2^k` unitary matrix `U`");
oracle gates are always valid. -/
def Valid (f : Str → ℝ) {N : ℕ} : UGate N → Prop
  | .expl k _ ent => decodeU f ent ∈ Matrix.unitaryGroup (Bits k) ℂ
  | _ => True

/-- The gate is allowed in an `L`-oracle circuit in the sense of Definition 4.4 (p. 14): an
explicit gate, or an uncontrolled oracle gate `O_m` itself. -/
def IsPlain {N : ℕ} : UGate N → Prop
  | .expl _ _ _ => True
  | .orac κ _ _ => κ = .plain
  | .corac _ _ _ => False

end UGate

/-- **An `𝒪`-oracle unitary quantum circuit** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2, 4.3 and 5.5, pp. 14
and 17): a number `N` of qubits and a finite sequence of gates, applied first to last. -/
structure UCircuit where
  N : ℕ
  gates : List (UGate N)

namespace UCircuit

/-- The descriptions of the gates. -/
def gateCodes (C : UCircuit) : List Str := C.gates.map UGate.code

/-- The description of the circuit: the number of qubits in binary followed by the gate
descriptions ("the total length of the gate descriptions together with the qubit labels",
Definition 4.2). -/
def code (C : UCircuit) : Str := tup (Nat.bits C.N :: C.gateCodes)

/-- The unitary defined by the circuit, "obtained by taking the product of the unitaries"
(Definition 4.3, p. 14), the first gate rightmost, with explicit global phase. -/
noncomputable def unitary (C : UCircuit) (f : Str → ℝ) (O : ULang) : Matrix (Bits C.N) (Bits C.N) ℂ :=
  C.gates.foldl (fun acc g => g.mat f O * acc) 1

/-- Every explicit gate describes a unitary matrix under `f`. -/
def Valid (C : UCircuit) (f : Str → ℝ) : Prop := ∀ g ∈ C.gates, g.Valid f

/-- Every oracle gate is an uncontrolled `O_m` (an `L`-oracle circuit of Definition 4.4). -/
def Plain (C : UCircuit) : Prop := ∀ g ∈ C.gates, g.IsPlain

end UCircuit

end KTUnitary.Synth


