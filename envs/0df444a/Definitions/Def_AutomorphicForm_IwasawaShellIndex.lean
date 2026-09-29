-- Prove2me | Definitions.Def_AutomorphicForm_IwasawaShellIndex
-- name    : AutomorphicForm_IwasawaShellIndex
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d22a6228-6f13-5f4e-b1b0-10f18fae23de
-- title:
--   Iwasawa shell index of an adelic GL(2) element at a place
-- statement:
--   Over a number field $K$, with $v$ a nonzero prime of $\mathcal{O}_K$, this module attaches to each $g \in \mathrm{GL}_2(\mathbb{A}_K)$ (the group `AdelicGL2`, the general linear group of degree $2$ over the adele ring $\mathbb{A}_K = \mathbb{A}_{K,\infty} \times \mathbb{A}_{K,\mathrm{fin}}$) an integer recording which Iwasawa shell its component at $v$ lies in. The basic pieces are `adeleEvalFin`, the ring homomorphism $\mathbb{A}_K \to K_v$ taking an adele to the $v$-component of its finite part, and `localMatrix`, the entrywise image $g_v \in M_2(K_v)$ of the matrix of $g$ under this homomorphism; `finEntryValuation` and `finDetValuation` are the valuations, in $\mathbb{Z}^{\mathrm{m}}_{\ge 0} =$ `WithZero (Multiplicative ℤ)`, of an entry of $g$ and of $\det g$ at $v$. The index itself is
--   $$\mathtt{iwasawaShellIndex}\;K\;v\;g \;=\; 2\log\max\bigl(|g_{10}|_v, |g_{11}|_v\bigr) - \log|\det g|_v \;=\; \mathrm{ord}_v(\det g_v) - 2\min\bigl(\mathrm{ord}_v g_{10}, \mathrm{ord}_v g_{11}\bigr),$$
--   where $\log$ is the isomorphism of the value group with $\mathbb{Z}$ normalised by $|x|_v = \exp(-\mathrm{ord}_v x)$.
--
--   The accompanying lemmas record: multiplicativity of $g \mapsto g_v$; nonvanishing of $\det g_v$, hence of $|\det g|_v$ and of the maximum of the two bottom-row valuations (the bottom row of an invertible $2\times 2$ matrix cannot be zero); the reformulation of the index in terms of $g_v$; and the characterisation of the vanishing of the index by the equation $|\det g|_v = \max(|g_{10}|_v, |g_{11}|_v)^2$, stated both through the auxiliary valuations and directly in terms of the valuations of the adelic entries. A transfer lemma computes the index of $g'$ from that of $g$ when $g'_v$ has the same bottom row as $g_v$ and $\det g'_v = a \det g_v$ with $a \neq 0$, the index dropping by $\log|a|_v$. From it follow the invariance of the index under left multiplication by an adelic central scalar `centralScalar`, by an adelic upper unipotent matrix `unipotentGL2 x`, and by the Hecke generator `heckeGen` at a prime $w \neq v$ (whose $v$-component is the identity), together with the computation that left multiplication by `heckeGen` at $v$, whose $v$-component is $\mathrm{diag}(\varpi_v, 1)$, increases the index by one.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the completions $K_v$ with their valuations, and the $\log$/$\exp$ maps on `WithZero (Multiplicative ℤ)`; the local component homomorphism, the local matrix and the Iwasawa shell index are the project's own constructions.
--
--   **Where it is used.** These definitions belong to the adelic automorphic-form infrastructure for $\mathrm{GL}_2$: the index partitions $\mathrm{GL}_2(\mathbb{A}_K)$ into the double cosets $Z_v N_v \,\mathrm{diag}(\varpi_v^m, 1)\, \mathrm{GL}_2(\mathcal{O}_v)$, and the invariance and shift lemmas are what is needed to handle central and unipotent translations and the action of Hecke generators on functions built from this decomposition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_IwasawaShellIndex.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]

def finEntryValuation (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    WithZero (Multiplicative ℤ) :=
  Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v)

def finDetValuation (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : WithZero (Multiplicative ℤ) :=
  Valued.v (((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v)

def iwasawaShellIndex (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : ℤ :=
  2 * WithZero.log (max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1)) -
    WithZero.log (finDetValuation K v g)

variable {K}

section Lemmas

variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

def adeleEvalFin : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)

theorem adeleEvalFin_apply (x : AdeleRing (𝓞 K) K) : adeleEvalFin v x = x.2 v := rfl

def localMatrix : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) :=
  (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).map (adeleEvalFin v)

theorem localMatrix_apply (i j : Fin 2) :
    localMatrix v g i j = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := rfl

theorem localMatrix_mul (h : AdelicGL2 (𝓞 K) K) : localMatrix v (g * h) = localMatrix v g * localMatrix v h := by
  rw [localMatrix, Matrix.GeneralLinearGroup.coe_mul, Matrix.map_mul]; rfl

theorem finEntryValuation_eq (i j : Fin 2) : finEntryValuation K v g i j = Valued.v (localMatrix v g i j) := rfl

theorem finDetValuation_eq : finDetValuation K v g = Valued.v (localMatrix v g).det := by
  rw [finDetValuation, Matrix.GeneralLinearGroup.val_det_apply]
  show Valued.v (adeleEvalFin v (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) = _
  rw [RingHom.map_det]
  rfl

theorem det_localMatrix_ne_zero : (localMatrix v g).det ≠ 0 := by
  have h : (localMatrix v g).det = adeleEvalFin v ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) :
      AdeleRing (𝓞 K) K) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]; rfl
  rw [h]
  exact (Units.map (adeleEvalFin v : AdeleRing (𝓞 K) K →+* v.adicCompletion K).toMonoidHom
    (Matrix.GeneralLinearGroup.det g)).ne_zero

theorem finDetValuation_ne_zero : finDetValuation K v g ≠ 0 := by
  rw [finDetValuation_eq, Valuation.ne_zero_iff]; exact det_localMatrix_ne_zero v g

theorem max_finEntryValuation_ne_zero :
    max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1) ≠ 0 := by
  intro h
  have h0 : finEntryValuation K v g 1 0 = 0 := le_antisymm (le_of_max_le_left h.le) zero_le'
  have h1 : finEntryValuation K v g 1 1 = 0 := le_antisymm (le_of_max_le_right h.le) zero_le'
  rw [finEntryValuation_eq, Valuation.zero_iff] at h0 h1
  apply det_localMatrix_ne_zero v g
  rw [Matrix.det_fin_two, h0, h1]; ring

theorem iwasawaShellIndex_eq_zero_iff :
    iwasawaShellIndex K v g = 0 ↔
      finDetValuation K v g = (max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1)) ^ 2 := by
  have hM := max_finEntryValuation_ne_zero v g
  have hD := finDetValuation_ne_zero v g
  rw [iwasawaShellIndex, sub_eq_zero]
  constructor
  · intro h
    have h' : WithZero.log (finDetValuation K v g) =
        WithZero.log ((max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1)) ^ 2) := by
      rw [WithZero.log_pow, ← h]; simp [two_mul]
    rw [← WithZero.exp_log hD, ← WithZero.exp_log (pow_ne_zero 2 hM), h']
  · intro h
    rw [h, WithZero.log_pow]; simp [two_mul]

theorem iwasawaShellIndex_eq_zero_iff' :
    iwasawaShellIndex K v g = 0 ↔
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 :=
  iwasawaShellIndex_eq_zero_iff v g

theorem iwasawaShellIndex_eq :
    iwasawaShellIndex K v g =
      2 * WithZero.log (max (Valued.v (localMatrix v g 1 0)) (Valued.v (localMatrix v g 1 1))) -
        WithZero.log (Valued.v (localMatrix v g).det) := by
  rw [iwasawaShellIndex, finDetValuation_eq]; rfl

theorem iwasawaShellIndex_eq_of_localMatrix (g' : AdelicGL2 (𝓞 K) K) (a : v.adicCompletion K) (ha : a ≠ 0)
    (hrow : ∀ j : Fin 2, localMatrix v g' 1 j = localMatrix v g 1 j)
    (hdet : (localMatrix v g').det = a * (localMatrix v g).det) :
    iwasawaShellIndex K v g' = iwasawaShellIndex K v g - WithZero.log (Valued.v a) := by
  rw [iwasawaShellIndex_eq, iwasawaShellIndex_eq, hrow 0, hrow 1, hdet, Valuation.map_mul,
    WithZero.log_mul ((Valuation.ne_zero_iff _).mpr ha)
      ((Valuation.ne_zero_iff _).mpr (det_localMatrix_ne_zero v g))]
  ring

theorem iwasawaShellIndex_centralScalar_mul (u : (AdeleRing (𝓞 K) K)ˣ) :
    iwasawaShellIndex K v (centralScalar (𝓞 K) K u * g) = iwasawaShellIndex K v g := by
  set uv : v.adicCompletion K := adeleEvalFin v (u : AdeleRing (𝓞 K) K) with huv_def
  have huv : uv ≠ 0 := (Units.map (adeleEvalFin v : AdeleRing (𝓞 K) K →+* v.adicCompletion K).toMonoidHom u).ne_zero
  have hloc : localMatrix v (centralScalar (𝓞 K) K u * g) = uv • localMatrix v g := by
    rw [localMatrix_mul]
    have : localMatrix v (centralScalar (𝓞 K) K u) = Matrix.scalar (Fin 2) uv := by
      ext i j
      rw [localMatrix, centralScalar,
        show ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) from rfl,
        Matrix.scalar_apply, Matrix.scalar_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs <;> simp [huv_def]
    rw [this, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hvu : Valued.v uv ≠ 0 := (Valuation.ne_zero_iff _).mpr huv
  rw [iwasawaShellIndex_eq, iwasawaShellIndex_eq, hloc, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul, Valuation.map_mul, Valuation.map_mul, max_mul_mul_left, Matrix.det_smul, Fintype.card_fin,
    Valuation.map_mul, Valuation.map_pow,
    WithZero.log_mul hvu ((finEntryValuation_eq v g 1 0) ▸ (finEntryValuation_eq v g 1 1) ▸
      max_finEntryValuation_ne_zero v g),
    WithZero.log_mul (pow_ne_zero 2 hvu) ((Valuation.ne_zero_iff _).mpr (det_localMatrix_ne_zero v g)),
    WithZero.log_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem iwasawaShellIndex_unipotentGL2_mul (x : AdeleRing (𝓞 K) K) :
    iwasawaShellIndex K v (unipotentGL2 x * g) = iwasawaShellIndex K v g := by
  have hloc : localMatrix v (unipotentGL2 x) = !![1, adeleEvalFin v x; 0, 1] := by
    ext i j
    rw [localMatrix, Matrix.map_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp
  have h := iwasawaShellIndex_eq_of_localMatrix v g (unipotentGL2 x * g) 1 one_ne_zero
    (fun j => by
      rw [localMatrix_mul, hloc, Matrix.mul_apply, Fin.sum_univ_two]
      simp)
    (by rw [localMatrix_mul, hloc, Matrix.det_mul, Matrix.det_fin_two_of]; ring)
  rw [h, Valuation.map_one, WithZero.log_one, sub_zero]

theorem localMatrix_heckeGen_self :
    localMatrix v (heckeGen (𝓞 K) K v) =
      Matrix.diagonal ![((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K), 1] := by
  ext i j
  rw [localMatrix_apply, heckeGen, heckeGenAt_snd_apply_self]

theorem localMatrix_heckeGen_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : v ≠ w) :
    localMatrix v (heckeGen (𝓞 K) K w) = 1 := by
  ext i j
  rw [localMatrix_apply, heckeGen, heckeGenAt_snd_apply_of_ne _ hw]

theorem iwasawaShellIndex_heckeGen_mul :
    iwasawaShellIndex K v (heckeGen (𝓞 K) K v * g) = iwasawaShellIndex K v g + 1 := by
  have hϖ : ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := Units.ne_zero _
  have h := iwasawaShellIndex_eq_of_localMatrix v g (heckeGen (𝓞 K) K v * g) _ hϖ
    (fun j => by
      rw [localMatrix_mul, localMatrix_heckeGen_self, Matrix.diagonal_mul]
      simp)
    (by rw [localMatrix_mul, localMatrix_heckeGen_self, Matrix.det_mul, Matrix.det_diagonal]; simp)
  rw [h, valued_uniformizerUnit, WithZero.log_exp]
  ring

theorem iwasawaShellIndex_heckeGen_mul_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : v ≠ w) :
    iwasawaShellIndex K v (heckeGen (𝓞 K) K w * g) = iwasawaShellIndex K v g := by
  have h := iwasawaShellIndex_eq_of_localMatrix v g (heckeGen (𝓞 K) K w * g) 1 one_ne_zero
    (fun j => by rw [localMatrix_mul, localMatrix_heckeGen_of_ne v hw, one_mul])
    (by rw [localMatrix_mul, localMatrix_heckeGen_of_ne v hw, one_mul, one_mul])
  rw [h, Valuation.map_one, WithZero.log_one, sub_zero]

end Lemmas

end AutomorphicForm

end


