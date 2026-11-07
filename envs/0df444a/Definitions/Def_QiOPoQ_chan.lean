-- Prove2me | Definitions.Def_QiOPoQ_chan
-- name    : QiOPoQ_chan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:29.786527+00:00
-- url     : https://prove2.me/theorems/c0bdc5f2-be64-47dc-8fe6-508871b9b1eb
-- title:
--   The unitary, the channel and the measurement law of a circuit
-- statement:
--   The unitary $U_C=U_{g_s}\cdots U_{g_1}$ of a circuit is the ordered product of its gates, each acting on its own wires and as the identity elsewhere. The **channel** of $C$ is eq. (1) of the paper:
--
--   $$
--   C(\rho) := \mathrm{Tr}_{\mathrm{junk}}\big[U_C(\rho_{\mathrm{in}}\otimes|0^{n_{\mathrm{anc}}}\rangle\langle 0^{n_{\mathrm{anc}}}|_{\mathrm{anc}})U_C^\dagger\big].
--   $$
--
--   The probability that $C$ on a classical input $x$ produces the output string $z$ is the Born probability $\langle z|C(|x\rangle\langle x|)|z\rangle$, with output bit $j$ read from the $j$-th wire of the output register.
--
--   **Formalization Note** `chanAs C n m` reads the channel as a map from $n$ to $m$ qubits; it is the zero map if the dimensions differ, and it is only used where they agree (the equalities are stated alongside).
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, eq. (1), p.13

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QiOPoQ_Circ

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms QAlgorithms.Complexity

variable {G : GateSet}

open Classical in
/-- A gate occurrence as a matrix on all `W` wires: gate `g.1` on the wires `g.2`, the identity
on the other wires. Entry `(y, y')` is `⟨y ∘ w|U|y' ∘ w⟩` when `y, y'` agree off the range of
`w`, else `0`. -/
noncomputable def gateMat {W : ℕ} (g : Σ i : Fin G.k, Fin (G.arity i) ↪ Fin W) :
    Matrix (Fin W → Bool) (Fin W → Bool) ℂ :=
  Matrix.of fun y y' =>
    if ∀ a, a ∉ Set.range g.2 → y a = y' a then G.mat g.1 (fun j => y (g.2 j)) (fun j => y' (g.2 j))
    else 0

/-- The unitary `U_C = U_{g_s} ⋯ U_{g_1}` of a circuit (first gate applied first). -/
noncomputable def circUnitary (C : Circ G) : Matrix (Fin (C.nin + C.nanc) → Bool)
    (Fin (C.nin + C.nanc) → Bool) ℂ :=
  C.gates.foldl (fun U g => gateMat g * U) 1

/-- The isometry `|x⟩ ↦ |x⟩_in ⊗ |0^{n_anc}⟩_anc`. -/
noncomputable def inMat (C : Circ G) : Matrix (Fin (C.nin + C.nanc) → Bool) (Fin C.nin → Bool) ℂ :=
  Matrix.of fun y x => if y = Fin.append x (fun _ : Fin C.nanc => false) then 1 else 0

open Classical in
/-- **The channel of a circuit, eq. (1), p.13:**
`C(ρ) := Tr_junk[U_C(ρ_in ⊗ |0^{n_anc}⟩⟨0^{n_anc}|_anc)U_C†]`, a superoperator from the `n_in`
input qubits to the `n_out` output qubits. The partial trace keeps the output wires `out` (in
order) and sums over the junk configurations. -/
noncomputable def chan (C : Circ G) : Superop (Fin C.nin → Bool) (Fin C.out.length → Bool) :=
  fun ρ =>
    let V := circUnitary C * inMat C
    let σ := V * ρ * V.conjTranspose
    Matrix.of fun z z' => ∑ y, ∑ y',
      if (fun j => y (C.out.get j)) = z ∧ (fun j => y' (C.out.get j)) = z' ∧
          (∀ a, a ∉ C.out → y a = y' a) then σ y y' else 0

/-- The channel of `C` viewed as a map from `n` to `m` qubits; the zero map when
`(n_in, n_out) ≠ (n, m)`. Only used where the dimensions agree (they are stated alongside). -/
noncomputable def chanAs (C : Circ G) (n m : ℕ) : Superop (Fin n → Bool) (Fin m → Bool) :=
  if h : C.nin = n ∧ C.out.length = m then
    fun ρ =>
      Matrix.reindex (Equiv.arrowCongr (finCongr h.2) (Equiv.refl Bool))
        (Equiv.arrowCongr (finCongr h.2) (Equiv.refl Bool))
        (chan C (Matrix.reindex (Equiv.arrowCongr (finCongr h.1) (Equiv.refl Bool)).symm
          (Equiv.arrowCongr (finCongr h.1) (Equiv.refl Bool)).symm ρ))
  else fun _ => 0

/-- The probability that measuring the output register of `C` in the computational basis gives
`z`, on the basis input `|x⟩_in ⊗ |0⟩_anc` (Born rule on `C(|x⟩⟨x|)`). -/
noncomputable def outProb (C : Circ G) (x : Fin C.nin → Bool) (z : Fin C.out.length → Bool) : ℝ :=
  (chan C (Matrix.single x x 1) z z).re

/-- The probability that `C`, run on the classical input `x` (bit `i` of `x` on input wire `i`;
used with `x.length = n_in`), outputs the string `z` (output bit `j` = wire `out[j]`). -/
noncomputable def runProb (C : Circ G) (x z : Str) : ℝ :=
  ∑ z' : Fin C.out.length → Bool,
    if List.ofFn z' = z then outProb C (fun i => x.getD i.val false) z' else 0

end QiOPoQ


