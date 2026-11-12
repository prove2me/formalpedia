-- Prove2me | Definitions.Def_UnifLattice_FastVf_ROBP
-- name    : UnifLattice_FastVf_ROBP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:18:37.920917+00:00
-- url     : https://prove2.me/theorems/e4963d26-bfa0-4384-8ca8-a3b8f1312cef
-- title:
--   Ordered read-once branching programs (Definition 3.11): reading order, transition matrices, bookends, Ordering and Correctness
-- statement:
--   Let $\ell\ge0$ and $L=2^\ell$. A **branching program of width $w$** over $3\ell$ input bits is $(\pi,\{M_{\tau,b}\}_{\tau\in[3\ell],b\in\{0,1\}},s,t)$: a permutation $\pi:[3\ell]\to[3\ell]$ (the **reading order**: step $\tau$ reads bit $z_{\pi(\tau)}$), **transition matrices** $M_{\tau,b}\in\{0,1\}^{w\times w}$ and **bookend vectors** $s,t\in\{-1,0,1\}^w$. Its value on $z\in\{0,1\}^{3\ell}$ is
--   $$s^{\mathsf T}M_{1,z_{\pi(1)}}M_{2,z_{\pi(2)}}\cdots M_{3\ell,z_{\pi(3\ell)}}\,t\in\mathbb Z .$$
--   Definition 3.11 (pp. 23–24): $g:[L]^3\to\{-1,0,1\}$ is computed by an **ordered read-once branching program** of width $w$ if there is such a program with
--   - **Correctness:** $g(i,j,k)=s^{\mathsf T}M_{1,z_{\pi(1)}}\cdots M_{3\ell,z_{\pi(3\ell)}}t$ for all $(i,j,k)\in[L]^3$, where $z$ is the bit string associated with $(i,j,k)$;
--   - **Ordering:** for all $t\in[\ell-1]$, $\pi^{-1}(t)<\pi^{-1}(t+1)$, $\pi^{-1}(\ell+t)<\pi^{-1}(\ell+t+1)$ and $\pi^{-1}(2\ell+t)<\pi^{-1}(2\ell+t+1)$ (the bits of $i$, of $j$ and of $k$ are each read left to right).
--
--   These programs describe the wiring functions for which the goal computes $V_f$ quickly.
--
--   **Formalization Note.** Steps and bit positions are 0-based (`Fin (3 * ℓ)`); the Ordering clause `IsOrderedPerm ℓ π` quantifies over `t` with `t + 1 < ℓ`, the paper's $t+1\in[\ell-1]$. Bits are `Fin 2`, $\{-1,0,1\}$ is Mathlib's `SignType` cast to `ℤ`, and the matrix product is taken in step order (`List.prod`). `B.value i j k` is the program's value on the bit string associated with $(i,j,k)$; `B.Ordered` is the Ordering clause, and `B.Computes g` is Definition 3.11 (Correctness and Ordering). With $\ell=0$ the program has no steps and its value is $s^{\mathsf T}t$.
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), pp. 23-24, Definition 3.11

import Mathlib
import Definitions.Def_UnifLattice_FastVf_Notation

open Matrix

/-!
# Ordered read-once branching programs (Definition 3.11)

Wee, Wichs, Wu, *SNARGs and ABE for Uniform Computations via Lattice Encodings*, STOC 2027
submission (manuscript sha256 fd77662e…), pp. 23–24, Definition 3.11.

A program of width `w` over `3ℓ` input bits is `(π, {M_{τ,b}}, s, t)`: a reading order
`π : [3ℓ] → [3ℓ]` (a permutation; step `τ` reads bit `z_{π(τ)}`), transition matrices
`M_{τ,b} ∈ {0,1}^{w×w}` and bookend vectors `s, t ∈ {−1,0,1}^w`. Steps and bit positions are
0-based (`Fin (3 * ℓ)`), bits are `Fin 2`, and `{−1, 0, 1}` is Mathlib's `SignType`.
-/

namespace UnifLattice.FastVf

/-- A (matrix) branching program `(π, {M_{τ,b}}_{τ ∈ [3ℓ], b ∈ {0,1}}, s, t)` of width `w` over
`3ℓ` input bits (Definition 3.11). -/
structure ROBP where
  /-- `ℓ`, with `L = 2^ℓ` and `3ℓ` input bits. -/
  ℓ : ℕ
  /-- The width `w`. -/
  w : ℕ
  /-- The reading order `π`, a permutation of `[3ℓ]`. -/
  π : Equiv.Perm (Fin (3 * ℓ))
  /-- The transition matrices `M_{τ,b} ∈ {0,1}^{w×w}`. -/
  M : Fin (3 * ℓ) → Fin 2 → Matrix (Fin w) (Fin w) (Fin 2)
  /-- The bookend vector `s ∈ {−1,0,1}^w`. -/
  s : Fin w → SignType
  /-- The bookend vector `t ∈ {−1,0,1}^w`. -/
  t : Fin w → SignType

/-- The Ordering clause of Definition 3.11 (p. 24) for a reading order `π` of `[3ℓ]`: for all
`t ∈ [ℓ − 1]`, `π⁻¹(t) < π⁻¹(t+1)`, `π⁻¹(ℓ+t) < π⁻¹(ℓ+t+1)` and `π⁻¹(2ℓ+t) < π⁻¹(2ℓ+t+1)`.
With 0-based positions the paper's `t ∈ {1, …, ℓ−1}` is `t + 1` for `t + 1 < ℓ` here. -/
def IsOrderedPerm (ℓ : ℕ) (π : Equiv.Perm (Fin (3 * ℓ))) : Prop :=
  ∀ (t : ℕ) (ht : t + 1 < ℓ),
    π.symm ⟨t, by omega⟩ < π.symm ⟨t + 1, by omega⟩ ∧
    π.symm ⟨ℓ + t, by omega⟩ < π.symm ⟨ℓ + t + 1, by omega⟩ ∧
    π.symm ⟨2 * ℓ + t, by omega⟩ < π.symm ⟨2 * ℓ + t + 1, by omega⟩

/-- `M_{τ,b}` as an integer matrix. -/
def ROBP.Mz (B : ROBP) (τ : Fin (3 * B.ℓ)) (b : Fin 2) : Matrix (Fin B.w) (Fin B.w) ℤ :=
  (B.M τ b).map fun x => (x.val : ℤ)

/-- `s` as an integer vector. -/
def ROBP.sz (B : ROBP) : Fin B.w → ℤ := fun a => ((B.s a : SignType) : ℤ)

/-- `t` as an integer vector. -/
def ROBP.tz (B : ROBP) : Fin B.w → ℤ := fun a => ((B.t a : SignType) : ℤ)

/-- The value of the program on `z ∈ {0,1}^{3ℓ}`:
`sᵀ M_{1, z_{π(1)}} M_{2, z_{π(2)}} ⋯ M_{3ℓ, z_{π(3ℓ)}} t ∈ ℤ` (the product in step order). -/
def ROBP.eval (B : ROBP) (z : Fin (3 * B.ℓ) → Fin 2) : ℤ :=
  B.sz ⬝ᵥ ((List.ofFn fun τ => B.Mz τ (z (B.π τ))).prod *ᵥ B.tz)

/-- The value of the program at `(i, j, k) ∈ [L]³`: its value on the bit string associated with
`(i, j, k)`. -/
def ROBP.value (B : ROBP) (i j k : Fin (2 ^ B.ℓ)) : ℤ :=
  B.eval (assocString B.ℓ i j k)

/-- The program is ordered (Ordering clause of Definition 3.11). -/
def ROBP.Ordered (B : ROBP) : Prop := IsOrderedPerm B.ℓ B.π

/-- Definition 3.11: `g : [L]³ → {−1,0,1}` (`L = 2^ℓ`) is computed by the ordered read-once
branching program `B` (with `B.ℓ = ℓ`): Correctness, `g(i, j, k) = sᵀ M_{1,z_{π(1)}} ⋯
M_{3ℓ,z_{π(3ℓ)}} t` for all `(i, j, k)` with associated bit string `z`, and Ordering. -/
def ROBP.Computes (B : ROBP) (g : Fin (2 ^ B.ℓ) → Fin (2 ^ B.ℓ) → Fin (2 ^ B.ℓ) → ℤ) : Prop :=
  (∀ i j k, g i j k = B.value i j k) ∧ B.Ordered

end UnifLattice.FastVf


