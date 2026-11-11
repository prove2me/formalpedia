-- Prove2me | Definitions.Def_LindbladQueryOptimal_Simulation_Combined
-- name    : LindbladQueryOptimal_Simulation_Combined
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:41.039745+00:00
-- url     : https://prove2.me/theorems/0e3ea279-d737-4af6-b7b2-dc769ebd4611
-- title:
--   Individual-oracle stacking and interleaved Hamiltonian/dissipative paths
-- statement:
--   Define the stacked access from the individual jump oracles, using the known amplitudes $\alpha_j/\sqrt{\Lambda_D}$, where $\Lambda_D=\sum_j\alpha_j^2$. Its input sector is swapped with this weighted zero-padded image and the individual oracles are selected on their respective orthogonal sectors. This is a fixed unitary extension of known state preparation followed by SELECT; no additional oracle is supplied.
--
--   The Hamiltonian embedding and rotation are exactly Eqs. (108), (111), (112). The combined local rotation applies the Hamiltonian stage first and the dissipative stage second and fixes every inactive sector. The private oracle is their direct sum. The regular and jump kernels are independently computed from local departures, complete intervening no-jump steps and local returns. The regular diagonal contains the same-time Hamiltonian-to-dissipative term $s_Ds_HV_0V_H^\dagger$; the jump kernel records the actual individual jump index in the departure-time history entry. The source operators act on the full padded registers before restriction to the valid future-zero coordinate span.
--
--   **Formalization Note.** A direct sum of the individual padded registers, with a separate reference input sector, realizes a known unitary extension of state preparation. Unused coordinates can be embedded into a qubit register and fixed by the oracle. This choice changes neither the encoded stacked operator nor the local operator identities or spectral bounds. The source domain for the stacked construction has a nonempty jump family and positive normalizations.
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Eqs. (3), (106)–(125), pp. 3, 27–32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Histories

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A reference input sector plus the padded individual-oracle sectors. All
extra coordinates are ordinary padding; no stacked oracle is supplied as input. -/
abbrev StackRegister (n m : ℕ) (a : Fin m → ℕ) := Sum (Bits n) (Σ j, Bits (a j))

def stackInput {n m : ℕ} {a : Fin m → ℕ} : Matrix (StackRegister n m a) (Bits n) ℂ :=
  inj0

def stackOutput {n m : ℕ} {a : Fin m → ℕ} :
    Matrix (StackRegister n m a) (Fin m × Bits n) ℂ := fun x y =>
  match x with
  | .inl _ => 0
  | .inr z => if z.1 = y.1 then padding n (a z.1) z.2 y.2 else 0

/-- Known state preparation amplitudes, Eq. (3). -/
def stackWeights {n m : ℕ} (a : Fin m → ℕ) (α : Fin m → ℝ) :
    Matrix (StackRegister n m a) (Bits n) ℂ := fun x y =>
  match x with
  | .inl _ => 0
  | .inr z => (α z.1 / Real.sqrt (dissipativeNormalization α) : ℝ) *
      padding n (a z.1) z.2 y

/-- One fixed unitary extension of the state preparation: swap the reference
input sector with its weighted image, fixing their orthogonal complement. -/
def stackPrepare {n m : ℕ} (a : Fin m → ℕ) (α : Fin m → ℝ) :
    Op (StackRegister n m a) :=
  let B := (stackInput : Matrix (StackRegister n m a) (Bits n) ℂ)
  let W := stackWeights a α
  1 - B*Bᴴ - W*Wᴴ + W*Bᴴ + B*Wᴴ

/-- Prepare the known weights and SELECT the individual oracles. -/
def stackOracle {n m : ℕ} (a : Fin m → ℕ) (α : Fin m → ℝ)
    (OL : ∀ j, Op (Bits (a j))) : Op (StackRegister n m a) :=
  Matrix.fromBlocks 1 0 0 (Matrix.blockDiagonal' OL) * stackPrepare a α

def stackedJump {n m : ℕ} (α : Fin m → ℝ) (L : Fin m → Op (Bits n)) :
    Matrix (Fin m × Bits n) (Bits n) ℂ := fun x y =>
  (Real.sqrt (dissipativeNormalization α) : ℂ)⁻¹ * L x.1 x.2 y

def hCos (δH : ℝ) : ℝ := (1-δH/2)/(1+δH/2)
def hSin (δH : ℝ) : ℝ := Real.sqrt (1 - hCos δH ^ 2)

def hEmbedding {n aH : ℕ} : Matrix (Sum (Bits aH) (Bits aH)) (Bits n) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromRows (padding n aH) (padding n aH)

/-- Eq. (112), not an assumed unitary or a supplied implementation. -/
def hRotation {n aH : ℕ} (δH : ℝ) : Op (Sum (Bits n) (Sum (Bits aH) (Bits aH))) :=
  let V := (hEmbedding : Matrix (Sum (Bits aH) (Bits aH)) (Bits n) ℂ)
  let P := V*Vᴴ
  Matrix.fromBlocks ((hCos δH : ℂ) • 1) ((-Complex.I*(hSin δH : ℂ)) • Vᴴ)
    ((hSin δH : ℂ) • V) (Complex.I • ((hCos δH : ℂ) • P + 1-P))

/-- Local Hamiltonian sector inserted in the no-jump public branch. -/
def hStageEmbedding {m : ℕ} {s h d : Type} :
    Matrix (Sum (LocalPublic m s) (Sum h d)) (Sum s h) ℂ := fun x y =>
  if x = (match y with | .inl z => .inl (.inl z) | .inr z => .inr (.inl z)) then 1 else 0

def dStageEmbedding {m : ℕ} {s h d : Type} :
    Matrix (Sum (LocalPublic m s) (Sum h d)) (Sum (LocalPublic m s) d) ℂ := fun x y =>
  if x = (match y with | .inl z => .inl z | .inr z => .inr (.inr z)) then 1 else 0

abbrev CombinedPrivate (n m aH : ℕ) (a : Fin m → ℕ) :=
  Sum (Sum (Bits aH) (Bits aH))
    (Sum (StackRegister n m a) (StackRegister n m a))

/-- Dissipative stage after Hamiltonian stage, retaining every inactive sector. -/
def combinedRotation {n m aH : ℕ} (a : Fin m → ℕ) (δH δD : ℝ) :
    Op (Sum (LocalPublic m (Bits n)) (CombinedPrivate n m aH a)) :=
  let EH := (hStageEmbedding : Matrix (Sum (LocalPublic m (Bits n)) (CombinedPrivate n m aH a)) (Sum (Bits n) (Sum (Bits aH) (Bits aH))) ℂ)
  let ED := (dStageEmbedding : Matrix (Sum (LocalPublic m (Bits n)) (CombinedPrivate n m aH a)) (Sum (LocalPublic m (Bits n))
    (Sum (StackRegister n m a) (StackRegister n m a))) ℂ)
  let RH := EH * hRotation (n := n) (aH := aH) δH * EHᴴ + (1-EH*EHᴴ)
  let RD := ED * rotation (stackInput : Matrix (StackRegister n m a) (Bits n) ℂ) (stackOutput : Matrix (StackRegister n m a) (Fin m × Bits n) ℂ) δD * EDᴴ + (1-ED*EDᴴ)
  RD * RH

def combinedOracle {n m aH : ℕ} (a : Fin m → ℕ) (α : Fin m → ℝ)
    (OH : Op (Bits aH)) (OL : ∀ j, Op (Bits (a j))) : Op (CombinedPrivate n m aH a) :=
  Matrix.fromBlocks (oracleLift OH) 0 0 (oracleLift (stackOracle a α OL))

/-- Exact diagonal correction (123), including the same-time H-to-D path. -/
def combinedDiagonal {n m aH : ℕ} (a : Fin m → ℕ) (δH δD : ℝ) :
    Op (CombinedPrivate n m aH a) :=
  let VH := (hEmbedding : Matrix (Sum (Bits aH) (Bits aH)) (Bits n) ℂ)
  let VD := V0 (stackInput : Matrix (StackRegister n m a) (Bits n) ℂ)
  Matrix.fromBlocks ((1-hCos δH : ℂ) • (VH*VHᴴ)) 0
    (((Real.sqrt δD * hSin δH : ℝ) : ℂ) • (VD*VHᴴ))
    ((1-Real.sqrt (1-δD) : ℂ) • (VD*VDᴴ))

def combinedP {n m aH : ℕ} (a : Fin m → ℕ) : Op (CombinedPrivate n m aH a) :=
  let V := V1 (stackOutput : Matrix (StackRegister n m a) (Fin m × Bits n) ℂ)
  Matrix.fromBlocks 0 0 0 (V*Vᴴ)

/-- Off-diagonal paths are defined from local departure and return amplitudes,
not as a residual of the global private-block identity. -/
def combinedDeltaR {n m aH r : ℕ} (a : Fin m → ℕ) (δH δD : ℝ) :
    Op (Valid r m (CombinedPrivate n m aH a)) :=
  let M := combinedRotation (n := n) (aH := aH) a δH δD
  let N : Matrix (CombinedPrivate n m aH a) (Bits n) ℂ := fun x y => M (.inr x) (.inl (.inl y))
  let E : Matrix (Bits n) (CombinedPrivate n m aH a) ℂ := fun x y => M (.inl (.inl x)) (.inr y)
  fun x y => if x.val.2.1 = y.val.2.1 then
    if x.val.1 = y.val.1 then combinedDiagonal a δH δD x.val.2.2 y.val.2.2
    else if y.val.1 < x.val.1 then
      ((hCos δH * Real.sqrt (1-δD))^(x.val.1.val-y.val.1.val-1) : ℝ) *
        (Complex.I • (N*E)) x.val.2.2 y.val.2.2
    else 0
  else 0

def combinedDeltaJ {n m aH r : ℕ} (a : Fin m → ℕ) (δH δD : ℝ) :
    Op (Valid r m (CombinedPrivate n m aH a)) :=
  let M := combinedRotation (n := n) (aH := aH) a δH δD
  let N : Matrix (CombinedPrivate n m aH a) (Bits n) ℂ := fun x y => M (.inr x) (.inl (.inl y))
  fun x y => if addsJump x.val.1 y.val.1 x.val.2.1 y.val.2.1 then
    let E : Matrix (Bits n) (CombinedPrivate n m aH a) ℂ := fun z w =>
      ∑ k : Fin m, if (k.val+1) = (x.val.2.1 y.val.1).val then
        M (.inl (.inr (k,z))) (.inr w) else 0
    ((hCos δH * Real.sqrt (1-δD))^(x.val.1.val-y.val.1.val-1) : ℝ) *
      (Complex.I • (N*E)) x.val.2.2 y.val.2.2
  else 0

end LindbladQueryOptimal.Simulation


