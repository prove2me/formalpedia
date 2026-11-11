-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Hybrids
-- name    : EFI1PRS_Uniform_Hybrids
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:57:30.405741+00:00
-- url     : https://prove2.me/theorems/3131ccc4-5e74-4abd-b6fd-6e3c6a059363
-- title:
--   Full public-register hybrids and exact length accounting
-- statement:
--   The hybrid $\mathcal H_i$ publishes every raw seed and retains all independent shifts, applies the first $i$ seeded extraction maps to the actual grouped prefix, and appends independent maximally mixed later retained columns. The state $\mathcal W_i$ uses the corresponding witness prefix instead. Both are evaluated from explicit finite matrix formulas.
--
--   All lengths are charged: $q=Na+t\log_2M$, $d=N(t-\ell)+Mt$, $r=q+Lt+2d$ and $n=q+MLt$. The mask operator is $P_{u,v}=\bigotimes_j X^{u_j}Z^{v_j}$; $d=0$ gives the scalar identity. The source stretch identity is a theorem obligation, not a defining assumption.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, §5, Eq. (5.1), pp.13–15

import Definitions.Def_EFI1PRS_Uniform_Extraction

/-! Batra, §5.1, equation (5.1), pp.13–14. The whole public raw seed
and every independent row shift remain in each hybrid. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def publicLength (g : PairPreparation) (sec : ℕ) : ℕ :=
  windowLength (sourceWidth g sec) * seedLength (rows (sourceWidth g sec) sec) sec +
    rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec)

def retainedWidth (g : PairPreparation) (sec : ℕ) : ℕ :=
  publicLength g sec + windowLength (sourceWidth g sec) * retained (sourceWidth g sec) sec

/-- X_i is selected when witness=false, and Z_i when witness=true. Seed bits
are copied as a basis register, whereas all quantum past coherences are kept. -/
def hybrid (g : PairPreparation) (sec i : ℕ) (witness : Bool) :
    Matrix (Qubits (retainedWidth g sec)) (Qubits (retainedWidth g sec)) ℂ :=
  let M := sourceWidth g sec
  let t := rows M sec
  let ell := retained M sec
  let N := windowLength M
  let a := seedLength t sec
  let shiftWidth := t*shiftBits M
  let X := if witness then witnessColumns g sec i else actualColumns g sec i
  fun x y =>
    if (∀ j : Fin (N*a), bitAt x j.val = bitAt y j.val) ∧
      (∀ j : Fin ((N-i)*ell),
        bitAt x (N*a+shiftWidth+i*ell+j.val) = bitAt y (N*a+shiftWidth+i*ell+j.val))
    then
      let S : Qubits (N*a) := fun j => bitAt x j.val
      ((2 : ℂ)^(N*a + (N-i)*ell))⁻¹ *
        extractedPrefix g sec i S X
          (fun j => bitAt x (N*a+j.val)) (fun j => bitAt y (N*a+j.val))
    else 0

def H (g : PairPreparation) (sec i : ℕ) := hybrid g sec i false
def W (g : PairPreparation) (sec i : ℕ) := hybrid g sec i true

def maskedWidth (g : PairPreparation) (sec : ℕ) : ℕ :=
  let M := sourceWidth g sec
  let t := rows M sec
  windowLength M*(t-retained M sec)+M*t

def constructionKeyLength (g : PairPreparation) (sec : ℕ) : ℕ :=
  publicLength g sec + copies (sourceWidth g sec)*rows (sourceWidth g sec) sec +
    2*maskedWidth g sec

def constructionOutputLength (g : PairPreparation) (sec : ℕ) : ℕ :=
  publicLength g sec + sourceWidth g sec * copies (sourceWidth g sec) * rows (sourceWidth g sec) sec

/-- X^u Z^v in each tensor factor; d=0 gives the scalar identity. -/
def pauliMask {d : ℕ} (u v : Qubits d) : Matrix (Qubits d) (Qubits d) ℂ :=
  fun x y => ∏ j, ((if u j then pauliX else 1) * (if v j then pauliZ else 1)) (x j) (y j)

end EFI1PRS.Uniform


