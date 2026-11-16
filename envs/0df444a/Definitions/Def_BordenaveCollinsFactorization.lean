-- Prove2me | Definitions.Def_BordenaveCollinsFactorization
-- name    : BordenaveCollinsFactorization
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-16T02:08:32.795722+00:00
-- url     : https://prove2.me/theorems/dad9b5e7-73ec-4884-b984-f3de017806ae
-- title:
--   Products of linear factors with matrix coefficients in unitary letters — definitions
-- statement:
--   Definitions for stating Pisier's factorization of a matrix-coefficient polynomial in unitaries into linear factors.
--
--   - `tOp A T` is $A \otimes T$ for an $m \times n$ complex matrix $A$ and a bounded operator $T : H_1 \to H_2$: the operator from $n$ copies of $H_1$ to $m$ copies of $H_2$ whose $(a, b)$ block is $A_{ab}\,T$.
--   - `amp ρ X` is $\sum_l X(l) \otimes \rho(l)$ for a finite family of operators $\rho(l)$ and matrices $X(l)$ of a common size.
--   - `evalW ρ w` is the product of the operators $\rho(l)$ over the letters $l$ of the word $w$, in order; `evalP ρ y` is $\sum_w y_w \otimes \rho(w)$ for a finitely supported family $y$ of $n \times n$ matrices indexed by words.
--   - `UnitaryLetters e` is the data making a family $e$ of operators on a Hilbert space a set of unitary letters: a letter $o$ with $e(o) = 1$, a map $l \mapsto l^{-1}$ on letters with $e(l^{-1}) = e(l)^*$, and every $e(l)$ unitary.
--   - `gChain e Dim A t k` is the product $X_t X_{t+1} \cdots X_{t+k-1}$ of the linear factors $X_j = \sum_l A_{j,l} \otimes e(l)$, where $A_{j,l}$ is a $\mathrm{Dim}(j) \times \mathrm{Dim}(j+1)$ matrix; `gChainOn e Dim A q h₁ hq` is $X_1 \cdots X_q$ regarded as an operator on $D$ copies of the space when $\mathrm{Dim}(1) = \mathrm{Dim}(1+q) = D$. `reindexCopies` is the identification of $n$ copies with $m$ copies along a bijection of the index sets, used for that.
--
--   **Formalization note.** Copies of a Hilbert space $H$ are the $\ell^2$ direct sum `PiLp 2 (fun _ : Fin n => H)`. The letter type and the Hilbert space of `UnitaryLetters`, `gChain` and `gChainOn` live in the lowest universe.
-- source:
--   Pisier, G., On a linearization trick, Enseign. Math. 64 (2018) 315–326, https://doi.org/10.4171/LEM/64-3/4-5, the objects of its factorization theorem (linear factors with matrix coefficients); cited as [59, Theorem 1] in Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), Lemma 9.1, p. 27

import Mathlib

/-!
# Pisier's factorization for unitary letters: definitions

Operators with matrix coefficients on finitely many copies of a Hilbert space, words and matrix
polynomials in a family of letters evaluated by a letter map, and products of linear factors
`X_j = ∑ₗ A_{j,l} ⊗ e(l)` with rectangular matrix coefficients.
-/

noncomputable section

namespace BordenaveCollins.Pisier

/-- Reindexing `n` copies of `H` as `m` copies along `Fin n ≃ Fin m`. -/
def reindexCopies {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n m : ℕ}
    (e : Fin n ≃ Fin m) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H e).toContinuousLinearEquiv.toContinuousLinearMap

/-- `A ⊗ T : H₁ⁿ → H₂ᵐ` for `T : H₁ → H₂`: the `(a, b)` block is `A a b • T`. -/
def tOp {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂) :
    PiLp 2 (fun _ : Fin n => H₁) →L[ℂ] PiLp 2 (fun _ : Fin m => H₂) :=
  ∑ a : Fin m, ∑ b : Fin n, A a b •
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => H₂)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.single ℂ (fun _ : Fin m => H₂) a).comp
        (T.comp (PiLp.proj 2 (fun _ : Fin n => H₁) b))))

/-- The amplification `∑ₗ X(l) ⊗ ρ(l)` of a letter map `ρ` at a matrix of letters `X`. -/
def amp {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {ι : Type*} [Fintype ι]
    (ρ : ι → H₁ →L[ℂ] H₂) {m n : ℕ} (X : ι → Matrix (Fin m) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin n => H₁) →L[ℂ] PiLp 2 (fun _ : Fin m => H₂) :=
  ∑ l, tOp (X l) (ρ l)

/-- A word in the letters evaluated by a letter map: the product of its letters in order. -/
def evalW {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : ι → H →L[ℂ] H) (w : List ι) : H →L[ℂ] H :=
  (w.map ρ).prod

/-- A formal `n × n` matrix polynomial evaluated by a letter map. -/
def evalP {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : ι → H →L[ℂ] H) {n : ℕ} (y : List ι →₀ Matrix (Fin n) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  ∑ w ∈ y.support, tOp (y w) (evalW ρ w)

/-- Unitary letters: a unit letter `o` with `e o = 1`, and every letter is a unitary whose
adjoint is again a letter. -/
structure UnitaryLetters {ι L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    [CompleteSpace L] (e : ι → L →L[ℂ] L) where
  o : ι
  e_o : e o = 1
  inv : ι → ι
  e_inv : ∀ l, e (inv l) = star (e l)
  unitary : ∀ l, e l ∈ unitary (L →L[ℂ] L)

/-- The product `X_t X_{t+1} ⋯ X_{t+k-1}` of linear factors `X_j = ∑ₗ A_{j,l} ⊗ e(l)`, where
`A_{j,l}` is a `Dim j × Dim (j + 1)` matrix. -/
def gChain {ι : Type} [Fintype ι] {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (e : ι → L →L[ℂ] L) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (t : ℕ) :
    ∀ k : ℕ, PiLp 2 (fun _ : Fin (Dim (t + k)) => L) →L[ℂ]
      PiLp 2 (fun _ : Fin (Dim t) => L)
  | 0 => ContinuousLinearMap.id ℂ _
  | k + 1 => (gChain e Dim A t k).comp (amp e (A (t + k)))

/-- `X₁ ⋯ X_q` on `D` copies of `L` when `Dim 1 = Dim (1 + q) = D`. -/
def gChainOn {ι : Type} [Fintype ι] {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (e : ι → L →L[ℂ] L) {D : ℕ} (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (q : ℕ)
    (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D) :
    PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L) :=
  (reindexCopies (finCongr h₁)).comp ((gChain e Dim A 1 q).comp (reindexCopies (finCongr hq).symm))

end BordenaveCollins.Pisier

end


