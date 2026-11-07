-- Prove2me | Definitions.Def_KTUnitary_Synth_QCircuit
-- name    : KTUnitary_Synth_QCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:23.086635+00:00
-- url     : https://prove2.me/theorems/27917e47-2c7a-4838-afbe-b029ff702e78
-- title:
--   Oracle quantum circuit with CPTP gates
-- statement:
--   An **$L$-oracle quantum circuit** on $N$ qubits is a finite sequence of gates, each of which is
--   1. an explicitly specified $k$-qubit channel $\Lambda$ on $k$ distinct wires, given by its matrix $S_{ij,k\ell}=\langle i|\Lambda(|k\rangle\langle\ell|)|j\rangle$ on the operator basis, each entry written as $f(x)+f(y)\,i$ for the family's FPTEAS encoding $f$; or
--   2. an oracle gate $U_m$ of $L$ on $m$ distinct wires, acting as $\rho\mapsto U_m\rho U_m^\dagger$.
--
--   The circuit computes the composition of the gate channels, first gate first, each explicit channel applied as $\Lambda\otimes\mathrm{id}$. It is **valid** for $f$ if every explicit gate is completely positive (its Choi matrix is positive semidefinite) and trace preserving.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2 and 4.4, p. 14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_embedGate
import Definitions.Def_KTUnitary_Synth_allBits

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **A gate of an `L`-oracle quantum circuit on `N` qubits** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2 and 4.4,
p. 14).

* `expl k w ent`: an explicitly specified `k`-qubit channel `Λ` on the distinct wires `w`, given by
  its matrix `S` on the operator basis, `S_{ij,kℓ} = ⟨i|Λ(|k⟩⟨ℓ|)|j⟩`; the entry `S_{ij,kℓ}` is
  described by the pair of strings `ent (i, j) (k, ℓ) = (x, y)`, denoting `f(x) + f(y)·i` for the
  circuit's FPTEAS encoding `f`.
* `orac m w`: the oracle gate `U_m` of the language `L` (Definition 4.4: `U_m |x, b⟩ = |x, b ⊕ L(x)⟩`)
  on the `m` distinct wires `w`, acting as the unitary channel `ρ ↦ U_m ρ U_m^†`. "These oracle gates
  are specified only by the qubits acted upon." -/
inductive QGate (N : ℕ)
  | expl (k : ℕ) (w : Fin k ↪ Fin N) (ent : Bits k × Bits k → Bits k × Bits k → Str × Str)
  | orac (m : ℕ) (w : Fin m ↪ Fin N)

/-- The matrix `S` described by the entry strings `ent` under the encoding `f`. -/
noncomputable def decodeS (f : Str → ℝ) {k : ℕ} (ent : Bits k × Bits k → Bits k × Bits k → Str × Str) :
    Bits k × Bits k → Bits k × Bits k → ℂ :=
  fun a b => (f (ent a b).1 : ℂ) + (f (ent a b).2 : ℂ) * Complex.I

namespace QGate

/-- The description of a gate: a tag, the size, the wire labels in binary and, for an explicit
gate, the `2 · 16^k` entry strings in the order of `allBits k`. -/
def code {N : ℕ} : QGate N → Str
  | .expl k w ent => tup ([false] :: Nat.bits k :: (List.ofFn fun q => Nat.bits (w q)) ++
      ((allBits k).flatMap fun i => (allBits k).flatMap fun j => (allBits k).flatMap fun a =>
        (allBits k).flatMap fun b => [(ent (i, j) (a, b)).1, (ent (i, j) (a, b)).2]))
  | .orac m w => tup ([true] :: Nat.bits m :: List.ofFn fun q => Nat.bits (w q))

open Classical in
/-- The channel of a gate on `N`-qubit matrices: `Λ ⊗ id` with `Λ` on the wires `w`, i.e.
`(Λ ⊗ id)(X)_{ij} = Σ_{a,b} S_{(i∘w)(j∘w),(a∘w)(b∘w)} X_{ab}` over the `a` agreeing with `i` and the
`b` agreeing with `j` off the range of `w`; or `X ↦ U X U^†` for the embedded oracle unitary `U`. -/
noncomputable def apply (f : Str → ℝ) (L : Oracle) {N : ℕ} :
    QGate N → Matrix (Bits N) (Bits N) ℂ → Matrix (Bits N) (Bits N) ℂ
  | .expl _ w ent => fun X => Matrix.of fun i j => ∑ a : Bits N, ∑ b : Bits N,
      if (∀ q, q ∉ Set.range w → a q = i q) ∧ (∀ q, q ∉ Set.range w → b q = j q) then
        decodeS f ent (fun r => i (w r), fun r => j (w r)) (fun r => a (w r), fun r => b (w r)) * X a b
      else 0
  | .orac m w => fun X =>
      embedGate w (emb L m : Matrix (Bits m) (Bits m) ℂ) * X *
        (embedGate w (emb L m : Matrix (Bits m) (Bits m) ℂ)).conjTranspose

open scoped ComplexOrder in
/-- An explicit gate is valid for `f` if the map it describes is completely positive and trace
preserving ("a CPTP map on `2^k × 2^k` density matrices", Definition 4.2): its Choi matrix
`J_{(k,i),(ℓ,j)} = S_{ij,kℓ}` is positive semidefinite, and `Tr Λ(|k⟩⟨ℓ|) = [k = ℓ]`. Oracle gates
are always valid. -/
def Valid (f : Str → ℝ) {N : ℕ} : QGate N → Prop
  | .expl k _ ent =>
      (Matrix.of fun a b : Bits k × Bits k => decodeS f ent (a.2, b.2) (a.1, b.1)).PosSemidef ∧
      ∀ a b : Bits k, ∑ i : Bits k, decodeS f ent (i, i) (a, b) = if a = b then 1 else 0
  | .orac _ _ => True

end QGate

/-- **An `L`-oracle quantum circuit** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2 and 4.4, p. 14): a number `N` of
qubits and a finite sequence of gates, applied first to last. -/
structure QCircuit where
  N : ℕ
  gates : List (QGate N)

namespace QCircuit

/-- The descriptions of the gates. -/
def gateCodes (C : QCircuit) : List Str := C.gates.map QGate.code

/-- The description of the circuit: the number of qubits in binary followed by the gate
descriptions. -/
def code (C : QCircuit) : Str := tup (Nat.bits C.N :: C.gateCodes)

/-- The channel computed by the circuit: the composition of the gate channels, first gate first.
"We treat each gate description as specifying an exact channel" (Definition 4.2). -/
noncomputable def channel (C : QCircuit) (f : Str → ℝ) (L : Oracle) :
    Matrix (Bits C.N) (Bits C.N) ℂ → Matrix (Bits C.N) (Bits C.N) ℂ :=
  C.gates.foldl (fun acc g => g.apply f L ∘ acc) id

/-- Every explicit gate describes a CPTP map under `f`. -/
def Valid (C : QCircuit) (f : Str → ℝ) : Prop := ∀ g ∈ C.gates, g.Valid f

end QCircuit

end KTUnitary.Synth


