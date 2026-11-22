-- Prove2me | Definitions.Def_ShiTensor_Core
-- name    : ShiTensor_Core
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-13T03:33:11.424879+00:00
-- url     : https://prove2.me/theorems/28da5b1a-0b3a-4c37-b12a-0cfabdf18f73
-- title:
--   Amplitude-array tensor product of basis state vectors (definitions only)
-- statement:
--   Definitions only: the amplitude-array tensor product of computational-basis state vectors.
--
--   leftBits y and rightBits y read off the first m and last p bits of a joint index y : Bits (m + p), along Fin.castAdd and Fin.natAdd respectively; tensor psi phi is the joint state whose amplitude at y is psi (leftBits y) * phi (rightBits y).
--
--   This bundle deliberately contains NO theorem, so that every derivable fact remains separately submittable.
--
--   HONEST LIMITATIONS, stated in full in the module docstring. This is an amplitude-array product, NOT a bundled tensor product: there is no connection to Mathlib's TensorProduct, no universal property, no bilinear map, and no claim that QState (m + p) is spanned by such products. The bijection Bits (m + p) = Bits m x Bits p induced by leftBits/rightBits IS true but is NOT proved here, so every reindexing argument needs it supplied separately. No normalisation or unitarity is assumed: psi and phi are arbitrary functions to the complex numbers. Nothing connects tensor to runLayered, Instr.apply, embedCirc, inputState, outDist or acceptProb -- in particular the fact a caller most likely wants, that a circuit acting on disjoint wire blocks sends a product state to a product state so that acceptance probabilities multiply, is NOT here and does not follow from anything in this file. No independence interpretation is justified: there is no measure and no PMF anywhere. The splitting is positional and asymmetric, with no commutativity or associativity stated. Every limitation of Def_ShiShallow_Core applies, since Bits and QState come from there.

/-
# Amplitude-array tensor product of computational-basis state vectors

Splits a `Bits (m + p)` index into its left `Bits m` and right `Bits p` halves along
`Fin.castAdd` / `Fin.natAdd`, and defines the product state whose amplitude at a joint index
is the product of the two factor amplitudes.

## Main definitions

* `ShiTensor.leftBits y` -- the first `m` bits of `y : Bits (m + p)`, i.e. `y ∘ Fin.castAdd p`.
* `ShiTensor.rightBits y` -- the last `p` bits, i.e. `y ∘ Fin.natAdd m`.
* `ShiTensor.tensor ψ φ` -- the joint state `fun y => ψ (leftBits y) * φ (rightBits y)`.

## HONEST LIMITATIONS -- read before citing this as a tensor product

1. **This is an AMPLITUDE-ARRAY product, not a bundled tensor product.** There is NO connection
   to Mathlib's `TensorProduct`, no universal property, no bilinear map, and no claim that
   `QState (m + p)` is spanned by such products. `tensor` is a plain formula on functions.
2. **No bijectivity fact is proved here.** `leftBits` and `rightBits` are the two projections
   induced by `Fin.castAdd`/`Fin.natAdd`, and `y ↦ (leftBits y, rightBits y)` IS a bijection
   `Bits (m + p) ≃ Bits m × Bits p`, but that is NOT established in this file. Every reindexing
   argument over a joint index therefore needs that bijection supplied separately.
3. **No normalisation and no unitarity.** `ψ` and `φ` are arbitrary functions to `ℂ`, not unit
   vectors. Nothing here says the tensor of normalised states is normalised; that requires the
   reindexing of limitation 2 and is a separate theorem.
4. **Nothing connects `tensor` to circuit dynamics.** No relation to `runLayered`, `runLayer`,
   `Instr.apply`, `apply1`, `cnotState`, `embedCirc`, `inputState`, `outDist` or `acceptProb` is
   stated or proved. In particular the fact a caller most likely wants -- that a circuit acting
   on disjoint wire blocks maps a product state to a product state, so acceptance probabilities
   MULTIPLY -- is NOT here and does not follow from anything in this file.
5. **No independence interpretation is justified.** Calling `tensor` a product of "independent"
   registers is motivation, not mathematics: there is no measure, no `PMF`, and no probabilistic
   structure anywhere in this file.
6. **The splitting is positional and asymmetric.** `leftBits`/`rightBits` are tied to the
   specific `m + p` decomposition; no commutativity or associativity of `tensor` is stated, and
   `tensor ψ φ` and `tensor φ ψ` inhabit different types unless `m = p`.
7. **Every limitation of `Def_ShiShallow_Core` applies**, since `Bits` and `QState` come from
   there: gate set `H, S, T, X, CNOT` with no universality theorem, and single-output-wire
   acceptance with no intermediate measurement or mixed-state formalism.
8. **DEFINITIONS ONLY: this file contains no theorem or lemma.** Even the `rfl`-restatement of
   `tensor` is omitted deliberately. A theorem placed inside a definition bundle is permanently
   unrecoverable, so every derivable fact above must be a SEPARATE theorem submission.
-/
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

/-- The first `m` bits of a joint index `y : Bits (m + p)`, read along `Fin.castAdd p`. -/
def leftBits {m p : ℕ} (y : Bits (m + p)) : Bits m := fun i => y (Fin.castAdd p i)

/-- The last `p` bits of a joint index `y : Bits (m + p)`, read along `Fin.natAdd m`. -/
def rightBits {m p : ℕ} (y : Bits (m + p)) : Bits p := fun j => y (Fin.natAdd m j)

/-- The amplitude-array tensor product: the joint amplitude at `y` is the product of the left
factor's amplitude at `leftBits y` and the right factor's amplitude at `rightBits y`.

See the module docstring: this is a formula on functions, NOT a bundled tensor product, and
nothing here relates it to circuit dynamics or to normalisation. -/
def tensor {m p : ℕ} (ψ : QState m) (φ : QState p) : QState (m + p) :=
  fun y => ψ (leftBits y) * φ (rightBits y)

end ShiTensor


