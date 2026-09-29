-- Prove2me | Definitions.Def_NumberField_StandardGlobalAddChar
-- name    : NumberField_StandardGlobalAddChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/19f4071b-fd77-5fbf-8f6e-a573fe8265fb
-- title:
--   Adelic trace data and the standard additive character of F
-- statement:
--   The standing context is a number field $F$. The module introduces the structure `AdelicTraceData F`, a record of the data needed to transport the rational standard character $\psi_{\mathbb Q}$ (the character `psiQ` on $\mathbb A_{\mathbb Q}$, built from $\exp(+2\pi i\,\cdot)$ at the real place and $\exp(-2\pi i\,\cdot)$ at the finite places) to $F$. Its fields are: an additive group homomorphism `traceFin` from the finite adeles of $F$ to those of $\mathbb Q$; an additive group homomorphism `traceInf` between the infinite adele rings; two compatibility statements, carried as fields, asserting that each of the two maps sends the diagonal image of $x\in F$ to the diagonal image of $\mathrm{Tr}_{F/\mathbb Q}(x)$ (Mathlib's `Algebra.trace ℚ F`); continuity of both maps; and surjectivity of `traceInf`.
--
--   From a datum $T$ of this kind, `adelicTrace` is the product map $\mathbb A_F = \mathbb A_{F,\infty}\times \mathbb A_{F,\mathrm{fin}} \to \mathbb A_{\mathbb Q}$ given componentwise by `traceInf` and `traceFin`; it is continuous and again compatible with $\mathrm{Tr}_{F/\mathbb Q}$ on the diagonal. The character `psiK` is `psiQ` precomposed with `adelicTrace`. Three properties are proved: it is trivial on the image of $F$; it is continuous; and it is nontrivial — here surjectivity of `traceInf` produces $u_\infty$ with $\mathrm{Tr}(u_\infty)$ the diagonal image of $1/2$, and the adele $(u_\infty,0)$ has character value $\exp(\pi i) = -1$. These combine into `isGlobalAddChar_psiK`, a term of the project predicate `IsGlobalAddChar F`, whose fields are exactly principal invariance, continuity and nontriviality.
--
--   A helper records $\mathrm{Tr}_{\mathbb Q/\mathbb Q}(x) = x$; `ratTraceData` is the datum over $\mathbb Q$ with both trace maps the identity, and its associated character is `psiQ` itself. Constructing an `AdelicTraceData` for a general $F$ is not undertaken here.
--
--   **Relation to Mathlib.** The adele rings, `AddChar` and `Algebra.trace` are Mathlib's; Mathlib has no standard global additive character of the adele ring of a number field, and the packaging of the adelic trace as a structure, together with `psiK`, is the project's own. Note that the resulting character is the complex conjugate of Tate's normalisation, since `psiQ` uses $\exp(-2\pi i\,\cdot)$ at the finite places and $\exp(+2\pi i\,\cdot)$ at the real place.
--
--   **Where it is used.** The character `psiK` supplies the additive character argument required by the project's Whittaker coefficients of automorphic forms on $\mathrm{GL}_2$ over a number field, where principal invariance, continuity and nontriviality (the content of `IsGlobalAddChar`) are what the Fourier-expansion arguments use.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_StandardGlobalAddChar.lean

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace
open AutomorphicForm

noncomputable section

namespace NumberField.StandardAddChar

theorem trace_rat_apply (x : ℚ) : Algebra.trace ℚ ℚ x = x := by
  have h := Algebra.trace_algebraMap (R := ℚ) (S := ℚ) x
  rw [Module.finrank_self, one_smul] at h
  rw [show algebraMap ℚ ℚ x = x from by
    rw [eq_ratCast (algebraMap ℚ ℚ) x, Rat.cast_id]] at h
  exact h

variable (F : Type) [Field F] [NumberField F]

structure AdelicTraceData where

  traceFin : FiniteAdeleRing (𝓞 F) F →+ FiniteAdeleRing (𝓞 ℚ) ℚ

  traceInf : InfiniteAdeleRing F →+ InfiniteAdeleRing ℚ

  traceFin_algebraMap (x : F) : traceFin (algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
    = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F x)

  traceInf_algebraMap (x : F) : traceInf (algebraMap F (InfiniteAdeleRing F) x)
    = algebraMap ℚ (InfiniteAdeleRing ℚ) (Algebra.trace ℚ F x)

  continuous_traceFin : Continuous traceFin

  continuous_traceInf : Continuous traceInf

  traceInf_surjective : Function.Surjective traceInf

namespace AdelicTraceData

variable {F}
variable (T : AdelicTraceData F)

def adelicTrace : AdeleRing (𝓞 F) F →+ AdeleRing (𝓞 ℚ) ℚ :=
  AddMonoidHom.prodMap T.traceInf T.traceFin

theorem adelicTrace_apply (u : AdeleRing (𝓞 F) F) :
    T.adelicTrace u = (T.traceInf u.1, T.traceFin u.2) := rfl

theorem adelicTrace_algebraMap (x : F) :
    T.adelicTrace (algebraMap F (AdeleRing (𝓞 F) F) x)
      = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F x) := by
  refine Prod.ext ?_ ?_
  · exact T.traceInf_algebraMap x
  · exact T.traceFin_algebraMap x

theorem continuous_adelicTrace : Continuous T.adelicTrace :=
  T.continuous_traceInf.prodMap T.continuous_traceFin

def psiK : AddChar (AdeleRing (𝓞 F) F) ℂ :=
  psiQ.compAddMonoidHom T.adelicTrace

theorem psiK_apply (u : AdeleRing (𝓞 F) F) : T.psiK u = psiQ (T.adelicTrace u) := rfl

theorem psiK_algebraMap (x : F) : T.psiK (algebraMap F (AdeleRing (𝓞 F) F) x) = 1 := by
  rw [psiK_apply, adelicTrace_algebraMap]
  exact psiQ_algebraMap (Algebra.trace ℚ F x)

theorem continuous_psiK : Continuous T.psiK :=
  continuous_psiQ.comp T.continuous_adelicTrace

theorem psiK_ne_one : T.psiK ≠ 1 := by
  obtain ⟨uInf, huInf⟩ := T.traceInf_surjective (algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2))
  intro hcontra
  have h := congrArg (fun ψ : AddChar (AdeleRing (𝓞 F) F) ℂ =>
    ψ ((uInf, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) hcontra
  simp only [AddChar.one_apply] at h
  rw [psiK_apply, adelicTrace_apply, huInf, map_zero, psiQ_apply] at h
  rw [show (((algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2),
      (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : AdeleRing (𝓞 ℚ) ℚ)).1
      = algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2) from rfl] at h
  rw [show (((algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2),
      (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : AdeleRing (𝓞 ℚ) ℚ)).2
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl] at h
  rw [psiArch_algebraMap, AddChar.map_zero_eq_one, mul_one] at h
  rw [show (2 * Real.pi * Complex.I) * (((1 : ℚ)/2 : ℚ) : ℂ)
      = Real.pi * Complex.I by push_cast; ring] at h
  rw [Complex.exp_pi_mul_I] at h
  norm_num at h

theorem isGlobalAddChar_psiK : IsGlobalAddChar F T.psiK where
  principalInvariant := T.psiK_algebraMap
  continuous := T.continuous_psiK
  nontrivial := T.psiK_ne_one

end AdelicTraceData

def ratTraceData : AdelicTraceData ℚ where
  traceFin := AddMonoidHom.id _
  traceInf := AddMonoidHom.id _
  traceFin_algebraMap x := by
    rw [AddMonoidHom.id_apply]; congr 1; exact (trace_rat_apply x).symm
  traceInf_algebraMap x := by
    rw [AddMonoidHom.id_apply]; congr 1; exact (trace_rat_apply x).symm
  continuous_traceFin := continuous_id
  continuous_traceInf := continuous_id
  traceInf_surjective := Function.surjective_id

theorem ratTraceData_psiK : ratTraceData.psiK = psiQ := by
  ext u
  rfl

end NumberField.StandardAddChar

end


