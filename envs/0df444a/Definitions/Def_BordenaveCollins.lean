-- Prove2me | Definitions.Def_BordenaveCollins
-- name    : BordenaveCollins
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-16T02:08:15.813508+00:00
-- url     : https://prove2.me/theorems/f5e8b50a-9fcd-45a6-bec2-4b442c683f81
-- title:
--   Random permutations and perfect matchings converging to F_r * Γ_s — definitions
-- statement:
--   Definitions for the strong convergence of independent uniform random permutations and uniform random perfect matchings to the free product $F_r * \Gamma_s$, where $F_r$ is the free group on $r$ generators $u_1, \dots, u_r$ and $\Gamma_s$ is the free product of $s$ copies of $\mathbb Z/2$ with generators $m_1, \dots, m_s$.
--
--   - **Group and words.** `G r s` is $F_r * \Gamma_s$. A letter (`Lt r s`) is $u_i$, $u_i^{-1}$ or $m_j$; `genL` is its group element, `wprod` the product of a word in the order the letters appear, and `len g` the least length of a word with product $g$. `genO` extends `genL` to optional letters, the missing letter standing for the identity.
--   - **Random model.** A sample `Om r s N` is $r$ permutations and $s$ perfect matchings of $\{0, \dots, N-1\}$; a perfect matching is a fixed-point-free involution (`DerandSq.PM`). `Adm s N` says the size is admissible: any $N$ when $s = 0$, even $N$ otherwise. `act ω` is the homomorphism $F_r * \Gamma_s \to S_N$ sending $u_i$ to the $i$-th permutation and $m_j$ to the $j$-th matching (`invHom` is the homomorphism $\mathbb Z/2 \to S_N$ of an involution). `fixCount` counts fixed points and `expFix r s N g` is the average of the number of fixed points of `act ω g` over all samples (zero when there are no samples). `stp s` is $1$ if $s = 0$ and $2$ otherwise, so that $N = \mathrm{stp}(s)\,n$ runs through admissible sizes.
--   - **First-order coefficient.** `cfun g` is the number of triples $(k, z, a)$ with $k \ge 2$, $z \ne 1$, $g = a z^k a^{-1}$ and $\mathrm{len}(g) = 2\,\mathrm{len}(a) + k\,\mathrm{len}(z)$, minus $1$ if $g \ne 1$ and $g^2 = 1$. The length condition says that the product $a \cdot z \cdots z \cdot a^{-1}$ is reduced.
--   - **Matrix coefficients.** `MG D r s` is the group algebra of $F_r * \Gamma_s$ with coefficients in $M_D(\mathbb C)$. For a family of operators $\pi(g)$ on a Hilbert space $H$, `opOf π x` is $\sum_g x_g \otimes \pi(g)$ on $D$ copies of $H$, and `regOp x` is this operator for the left-regular representation on $\ell^2(F_r * \Gamma_s)$. `adj x` is $\sum_g x_g^* \, g^{-1}$ and `trTau x` is $\frac1D \operatorname{tr}(x_e)$, the normalized trace of the coefficient of the identity.
--   - **Linear factors.** `Lin r s` is a sequence of $D_m \times D_m$ matrix coefficients $B_{j,l}$, indexed by $j \in \mathbb N$ and an optional letter $l$, periodic in $j$ with period $q \ge 1$. `Xop L j` is $X_j = \sum_l B_{j,l} \otimes \lambda(g_l)$ on $D_m$ copies of $\ell^2(F_r * \Gamma_s)$, `Bprod L m i` is $B_{1,i_1} B_{2,i_2} \cdots B_{m,i_m}$, and `iprod i` is $g_{i_1} g_{i_2} \cdots g_{i_m}$.
--
--   **Formalization note.** The free product is `Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s)`. Indices start at $0$. The sequence $B_{j,l}$ is defined for every $j \ge 0$, and `Bprod` uses $j = 1, \dots, m$. The model follows Bordenave and Collins's strong convergence theorem for random permutations and matchings; `cfun`, `Lin`, `Xop` and `Bprod` are the objects of §5 and §9 of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence*, adapted from the free group to $F_r * \Gamma_s$.
-- source:
--   Bordenave, C. and Collins, B., Eigenvalues of random lifts and polynomials of random permutation matrices, Ann. of Math. (2) 190 (2019) 811–875, https://doi.org/10.4007/annals.2019.190.3.3, the objects of its strong convergence theorem for random permutations and matchings; with the notation of the proof method of Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), §5 and §9

import Mathlib
import Definitions.Def_DerandSq_Gam
import Definitions.Def_DerandSq_PM
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_L2
import Definitions.Def_DerandSq_leftReg
import Definitions.Def_AccessibleMaps_tensorOp

/-!
# Strong convergence of random permutations and perfect matchings: definitions

Definitions for the strong convergence of independent uniform random permutations and perfect
matchings of `Fin N` to the generators of `F_r * Γ_s` (after Bordenave–Collins): the group and its
letters, word length, the random model and its expected fixed-point counts, the first-order
coefficient `cfun`, the matrix-coefficient group algebra with its representations, adjoint and
trace, and periodic linearizations.
-/

open Finset

noncomputable section

namespace BordenaveCollins

/-- `F_r * Γ_s`. -/
abbrev G (r s : ℕ) := Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s)

/-- Letters: `inl (i, true)` is `u_i`, `inl (i, false)` is `u_i⁻¹`, `inr j` is `m_j`. -/
abbrev Lt (r s : ℕ) := (Fin r × Bool) ⊕ Fin s

/-- The group element of a letter. -/
def genL {r s : ℕ} : Lt r s → G r s
  | Sum.inl (i, true) => Monoid.Coprod.inl (FreeGroup.of i)
  | Sum.inl (i, false) => (Monoid.Coprod.inl (FreeGroup.of i))⁻¹
  | Sum.inr j => Monoid.Coprod.inr (DerandSq.mGen j)

/-- The group element of a word (product in the order the letters appear). -/
def wprod {r s : ℕ} (u : List (Lt r s)) : G r s := (u.map genL).prod

/-- Word length of a group element. -/
def len {r s : ℕ} (g : G r s) : ℕ := sInf {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}

/-- The first-order coefficient of `g`: the number of ways to write `g` as a reduced product
`a z^k a⁻¹` with `k ≥ 2`, `z ≠ 1` (reduced: `len g = 2 * len a + k * len z`), minus one if `g` is
an involution. -/
def cfun {r s : ℕ} (g : G r s) : ℤ := by
  classical exact
  (Nat.card {t : ℕ × G r s × G r s // 2 ≤ t.1 ∧ t.2.1 ≠ 1 ∧
      g = t.2.2 * t.2.1 ^ t.1 * t.2.2⁻¹ ∧ len g = 2 * len t.2.2 + t.1 * len t.2.1} : ℤ) -
    (if g ≠ 1 ∧ g * g = 1 then 1 else 0)

/-- A sample: `r` permutations and `s` perfect matchings of `Fin N`. -/
abbrev Om (r s N : ℕ) := (Fin r → Equiv.Perm (Fin N)) × (Fin s → DerandSq.PM N)

/-- The sizes for which the model is defined: all `N` if there are no matchings, even `N`
otherwise. -/
def Adm (s N : ℕ) : Prop := s = 0 ∨ Even N

/-- The homomorphism `Z₂ → Perm (Fin N)` of an involution. -/
def invHom {N : ℕ} (σ : DerandSq.PM N) : Multiplicative (ZMod 2) →* Equiv.Perm (Fin N) where
  toFun a := σ.1 ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have hσ : σ.1 * σ.1 = 1 := by
      ext x; simp [(σ.2 x).1]
    have key : ∀ a b : ZMod 2, σ.1 ^ (a + b).val = σ.1 ^ a.val * σ.1 ^ b.val := by
      intro a b
      have h2 : σ.1 ^ 2 = 1 := by rw [pow_two, hσ]
      fin_cases a <;> fin_cases b
      · show σ.1 ^ (0 : ZMod 2).val = σ.1 ^ (0 : ZMod 2).val * σ.1 ^ (0 : ZMod 2).val
        simp
      · show σ.1 ^ (1 : ZMod 2).val = σ.1 ^ (0 : ZMod 2).val * σ.1 ^ (1 : ZMod 2).val
        simp
      · show σ.1 ^ (1 : ZMod 2).val = σ.1 ^ (1 : ZMod 2).val * σ.1 ^ (0 : ZMod 2).val
        simp
      · show σ.1 ^ ((1 : ZMod 2) + 1).val = σ.1 ^ (1 : ZMod 2).val * σ.1 ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

/-- The representation of `G r s` on `Fin N` given by a sample. -/
def act {r s N : ℕ} (ω : Om r s N) : G r s →* Equiv.Perm (Fin N) :=
  Monoid.Coprod.lift (FreeGroup.lift ω.1) (Monoid.CoprodI.lift fun j => invHom (ω.2 j))

/-- Number of fixed points. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ := (univ.filter fun x => π x = x).card

/-- `E[fix(act ω g)]` over a uniform sample. -/
def expFix (r s N : ℕ) (g : G r s) : ℝ :=
  (∑ ω : Om r s N, (fixCount (act ω g) : ℝ)) / (Fintype.card (Om r s N) : ℝ)

/-- The step: `N = n` if there are no matchings, `N = 2n` otherwise. -/
def stp (s : ℕ) : ℕ := if s = 0 then 1 else 2

/-- `M_D(ℂ) ⊗ ℂ[F_r * Γ_s]`. -/
abbrev MG (D r s : ℕ) := MonoidAlgebra (Matrix (Fin D) (Fin D) ℂ) (G r s)

/-- `∑_g A_g ⊗ π(g)` on `D` copies of `H`. -/
def opOf {D r s : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G r s → H →L[ℂ] H) (x : MG D r s) :
    PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H) :=
  ∑ g ∈ x.coeff.support, AccessibleMaps.tensorOp (x.coeff g) (π g)

/-- `x` in the left-regular representation, on `D` copies of `ℓ²(G)`. -/
def regOp {D r s : ℕ} (x : MG D r s) :=
  opOf (fun g : G r s => DerandSq.leftReg g) x

/-- The group element of an optional letter (`none` is the identity). -/
def genO {r s : ℕ} : Option (Lt r s) → G r s
  | none => 1
  | some a => genL a

/-- A periodic family of square matrix coefficients: `B j l` is the coefficient of `λ(g_l)` in
the `j`-th linear factor `X_j`, with `X_{j+q} = X_j`. -/
structure Lin (r s : ℕ) where
  q : ℕ
  hq : 1 ≤ q
  Dm : ℕ
  B : ℕ → Option (Lt r s) → Matrix (Fin Dm) (Fin Dm) ℂ
  periodic : ∀ j l, B (j + q) l = B j l

/-- `X_j = ∑_l B_{j,l} ⊗ λ(g_l)` on `Dm` copies of `ℓ²(G)`. -/
def Xop {r s : ℕ} (L : Lin r s) (j : ℕ) :
    PiLp 2 (fun _ : Fin L.Dm => DerandSq.L2 (G r s)) →L[ℂ]
      PiLp 2 (fun _ : Fin L.Dm => DerandSq.L2 (G r s)) :=
  ∑ l : Option (Lt r s), AccessibleMaps.tensorOp (L.B j l) (DerandSq.leftReg (genO l))

/-- `B_{1,i₁} B_{2,i₂} ⋯ B_{m,i_m}`. -/
def Bprod {r s : ℕ} (L : Lin r s) (m : ℕ) (i : Fin m → Option (Lt r s)) :
    Matrix (Fin L.Dm) (Fin L.Dm) ℂ :=
  (List.ofFn fun j : Fin m => L.B ((j : ℕ) + 1) (i j)).prod

/-- `g_{i₁} g_{i₂} ⋯ g_{i_m}`. -/
def iprod {r s m : ℕ} (i : Fin m → Option (Lt r s)) : G r s :=
  (List.ofFn fun j : Fin m => genO (i j)).prod

/-- The adjoint `(∑ A_g g)* = ∑ A_gᴴ g⁻¹`. -/
def adj {D r s : ℕ} (x : MG D r s) : MG D r s :=
  x.coeff.sum fun g A => MonoidAlgebra.single g⁻¹ A.conjTranspose

/-- `(tr_D ⊗ τ)(x) = (1/D) tr (x_e)`. -/
def trTau {D r s : ℕ} (x : MG D r s) : ℂ := (D : ℂ)⁻¹ * Matrix.trace (x.coeff 1)

end BordenaveCollins

end


