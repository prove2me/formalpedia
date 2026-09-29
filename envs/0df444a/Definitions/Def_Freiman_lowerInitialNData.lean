-- Prove2me | Definitions.Def_Freiman_lowerInitialNData
-- name    : Freiman_lowerInitialNData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:51:18.245896+00:00
-- url     : https://prove2.me/theorems/71ae89f5-2f2d-45b3-9785-918300ad8c96
-- title:
--   Freiman initial contacts: lowerInitialNData
-- statement:
--   Actual source matrix products, recurrence ratios and exact finite Q(sqrt3) polynomial coefficient data for the eight H seam parameter boxes and three period contacts.
-- source:
--   Freiman report, prop:lc-H-contacts; certificates/initial_covers/parametric_h_seams.json and parametric_h_nseams.json; independent validator validate_h_seams_independent.py. Exact source hashes in INITIAL_CERTIFICATE_BINDING.json.

import Definitions.Def_Freiman_lowerInitialAlgebra
namespace Freiman
inductive LowerInitialNCase where
  | n13 | n14 | aux
  deriving DecidableEq

def lowerInitialNWords : LowerInitialNCase → Fin 4 → List ℕ+ × List ℕ+
  | .n13 => ![([3,2,1,1],[3,1,3,1,2,3,1,2,1,3]),([4,3,2,2],[3,1,3,3,1,2,1,3]),([3,2,1,1],[3,1,3,1,2,1,3]),([4,3,2,2],[3,1,2,1,3])]
  | .n14 => ![([3,2,1,1],[3,1,3,3,1,2,1,3]),([4,3,2,2],[3,3,1,2,1,3]),([3,2,1,1],[3,1,2,1,3]),([4,3,2,2],[3,1,2,1,3])]
  | .aux => ![([3,2,1,1],[3,1,3,1,2,1,3,1,2,3,1,2,1,3]),([4,3,2,2],[3,1,3,1,2,1,3,2,1,3]),([3,2,1,1],[3,1,3,1,2,1,3]),([4,3,2,2],[3,1,3,1,2,1,3])]

def lowerInitialNPolynomial : LowerInitialNCase → Fin 5 → CertField
  | .n13 => ![⟨16269946038488,11608044221690,0,0⟩,⟨-1399589413593656,-998559268745748,0,0⟩,⟨48440764081038,34611633304120,0,0⟩,⟨-558923786540,-399954471820,0,0⟩,⟨2149645382,1540567342,0,0⟩]
  | .n14 => ![⟨2378106295930,1648509127907,0,0⟩,⟨-204579200131398,-141813965666640,0,0⟩,⟨7715552912152,5276314006647,0,0⟩,⟨-96459908982,-65189783630,0,0⟩,⟨400014274,267547872,0,0⟩]
  | .aux => ![⟨146818924932561,389058227866166,0,0⟩,⟨-12629842507195946,-33468056619286666,0,0⟩,⟨440525600309736,1167326805681148,0,0⟩,⟨-5122729235550,-13574112784402,0,0⟩,⟨19857746975,52617325442,0,0⟩]

def lowerInitialNQuotient : LowerInitialNCase → Fin 3 → CertField
  | .n13 => ![⟨16269946038488,11608044221690,0,0⟩,⟨-374054283688,-267465680408,0,0⟩,⟨2149645382,1540567342,0,0⟩]
  | .n14 => ![⟨2378106295930,1648509127907,0,0⟩,⟨-62058681418,-42180666638,0,0⟩,⟨400014274,267547872,0,0⟩]
  | .aux => ![⟨146818924932561,389058227866166,0,0⟩,⟨-3414962995700,-9049022796390,0,0⟩,⟨19857746975,52617325442,0,0⟩]

def lowerInitialNBase : LowerInitialNCase → CertField
  | .n13 => ⟨(-1314314902057940728058477/3013077675712634737449394036379 : ℚ),(795520255394603644599767/3013077675712634737449394036379 : ℚ),0,0⟩
  | .n14 => ⟨(-6941529313302239422759/1568713047759220252327301162 : ℚ),(12884876409120362717389/4706139143277660756981903486 : ℚ),0,0⟩
  | .aux => ⟨(-6943050393994319141542214009/34207731569089345911378973922508143 : ℚ),(12118352686461209314065408448/102623194707268037734136921767524429 : ℚ),0,0⟩

noncomputable def lowerInitialNPolyEval (c : LowerInitialNCase) (x : ℝ) : ℝ :=
  ∑ i : Fin 5, certFieldVal (lowerInitialNPolynomial c i) * x^i.val
noncomputable def lowerInitialNQuotEval (c : LowerInitialNCase) (x : ℝ) : ℝ :=
  ∑ i : Fin 3, certFieldVal (lowerInitialNQuotient c i) * x^i.val
noncomputable def lowerInitialNMatrix (c : LowerInitialNCase) (i : Fin 4) (x : ℝ) : LowerInitialMatrix :=
  let w := lowerInitialNWords c i
  lowerInitialMatMul (lowerInitialMatMul (lowerInitialWordMatrix w.1)
    (lowerInitialP false x)) (lowerInitialWordMatrix w.2)
noncomputable def lowerInitialNNumerator (c : LowerInitialNCase) (x : ℝ) : ℝ :=
  ∑ i : Fin 4,
    let m := lowerInitialNMatrix c i x
    (if i.val < 2 then (1:ℝ) else -1) * (m.a*lowerTau+m.b) *
    ∏ j ∈ Finset.univ.erase i, lowerInitialMatDen (lowerInitialNMatrix c j x) lowerTau
noncomputable def lowerInitialNHolds (c : LowerInitialNCase) (n : ℕ) : Prop :=
  let w := lowerInitialNWords c
  prefixEval ((w 2).1 ++ lowerRepeat lowerPeriod n ++ (w 2).2) lowerTau +
  prefixEval ((w 3).1 ++ lowerRepeat lowerPeriod n ++ (w 3).2) lowerTau <
  prefixEval ((w 0).1 ++ lowerRepeat lowerPeriod n ++ (w 0).2) lowerTau +
  prefixEval ((w 1).1 ++ lowerRepeat lowerPeriod n ++ (w 1).2) lowerTau

def lowerInitialNCertificateValid (c : LowerInitialNCase) : Prop :=
  let Q := lowerInitialNQuotient c
  (lowerInitialNPolynomial c 0 = Q 0) ∧
  (lowerInitialNPolynomial c 1 = certFieldSub (Q 1) (certFieldScale 86 (Q 0))) ∧
  (lowerInitialNPolynomial c 2 = certFieldAdd (Q 0) (certFieldSub (Q 2) (certFieldScale 86 (Q 1)))) ∧
  (lowerInitialNPolynomial c 3 = certFieldSub (Q 1) (certFieldScale 86 (Q 2))) ∧
  (lowerInitialNPolynomial c 4 = Q 2) ∧
  0 < certFieldLower (Q 0) ∧ 0 < certFieldLower (certFieldScale (-1) (Q 1)) ∧
  0 < certFieldLower (Q 2) ∧
  0 < certFieldLower (certFieldAdd (Q 0) (certFieldScale (1/85) (Q 1))) ∧
  0 < certFieldLower (lowerInitialNBase c)
end Freiman


