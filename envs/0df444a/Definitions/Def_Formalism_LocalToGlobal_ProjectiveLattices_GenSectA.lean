-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:05.856353+00:00
-- url     : https://prove2.me/theorems/af84f58c-10d8-4a3c-ad05-4ddb262647d4
-- title:
--   Gen Sect A
-- statement:
--   Definitions and structural lemmas for Gen Sect A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
abbrev KT : Type := MvPolynomial (Fin (D + 1) × Fin m) K
abbrev KTf : Type := FractionRing (KT K D m)
abbrev ΩT : Type := MvPolynomial (Fin (D + 1) × Fin m) Ω
def ktToΩ : KT K D m →+* ΩT Ω D m := MvPolynomial.map (algebraMap K Ω)
def KTS : Submonoid (ΩT Ω D m) := (nonZeroDivisors (KT K D m)).map (ktToΩ K Ω D m)
abbrev RS : Type := Localization (KTS K Ω D m)
instance algKTR : Algebra (KTf K D m) (RS K Ω D m) :=
  (IsLocalization.map (M := nonZeroDivisors (KT K D m)) (T := KTS K Ω D m) (RS K Ω D m) (ktToΩ K Ω D m)
    (Submonoid.le_comap_map _) :
    KTf K D m →+* RS K Ω D m).toAlgebra
variable {K Ω D m}
def sec (x : Fin m → Ω) (i : Fin D) : ΩT Ω D m := ∑ j, X (i.succ, j) * C (x j)
variable (K) in

def Is (x : Fin m → Ω) : Ideal (RS K Ω D m) :=
  Ideal.span (Set.range fun i : Fin D => algebraMap (ΩT Ω D m) (RS K Ω D m) (sec x i))
def Zs (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : Prop := p.1 ≠ 0 ∧ p.2 = j₀
instance (j₀ : Fin m) : DecidablePred (Zs (D := D) j₀) := fun p => by unfold Zs; infer_instance
variable (Ω D) in

abbrev CT (j₀ : Fin m) : Type := MvPolynomial {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p} Ω
def xv (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if h : Zs j₀ p then 0 else X ⟨p, h⟩
def rr (x : Fin m → Ω) (j₀ : Fin m) (j : Fin m) : Ω := x j / x j₀
def gs (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if Zs j₀ p then -∑ k, xv j₀ (p.1, k) * C (rr x j₀ k) else xv j₀ p
def psi (x : Fin m → Ω) (j₀ : Fin m) : ΩT Ω D m →ₐ[Ω] CT Ω D j₀ := aeval (gs x j₀)
def incl (j₀ : Fin m) : CT Ω D j₀ →ₐ[Ω] ΩT Ω D m := rename Subtype.val
end Formalism.L2.Pj.GenSect


