-- Prove2me | Definitions.Def_LindbladQueryOptimal_Simulation_Local
-- name    : LindbladQueryOptimal_Simulation_Local
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:20.5832+00:00
-- url     : https://prove2.me/theorems/2c0c3a0d-b6d5-4d1e-ad22-b2c9da615771
-- title:
--   Local dissipative Kraus operators and Cayley rotation
-- statement:
--   For a rectangular operator $L$, positive normalization $\alpha$, and local step $\delta$, set $\nu=(1-\sqrt{1-\delta})/(1+\sqrt{1-\delta})$. This file computes the Kraus operators of Eq. (10), the resulting single-jump map, the Hermitian operator and oracle dilations, the complex and real Cayley transforms, and the padded embeddings $V_0,V_1$. In particular,
--   $$K_0=(I-\nu L^\dagger L/\alpha^2)(I+\nu L^\dagger L/\alpha^2)^{-1},\qquad K_1=-2i\sqrt\nu\,(L/\alpha)(I+\nu L^\dagger L/\alpha^2)^{-1}.$$
--   The three-sector rotation is exactly Eq. (46), including its norm-one jump-input transition. The catalyst is computed through the intermediate maps of Eqs. (43)–(45); no catalyst-preparation oracle or restoration identity is assumed.
--
--   These definitions support the local unitary, catalyst-restoration and error statements. Inverses have Lean's total semantics outside the stated parameter domain; the theorems use the source's positive normalization and small-step domain.
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), §2.2, pp. 7–8, Eqs. (7)–(12); §3.1, pp. 12–14, Eqs. (36)–(48); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Core

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

/-- Eqs. (8)--(10), total outside their stated domain. -/
def nu (δ : ℝ) : ℝ := (1 - Real.sqrt (1-δ))/(1 + Real.sqrt (1-δ))

def gram {a b : Type} [Fintype b] (L : Matrix b a ℂ) (α : ℝ) : Op a :=
  (α^2 : ℂ)⁻¹ • (Lᴴ * L)

def K0 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (L : Matrix b a ℂ) (α δ : ℝ) : Op a :=
  (1 - (nu δ : ℂ) • gram L α) * (1 + (nu δ : ℂ) • gram L α)⁻¹

def K1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (L : Matrix b a ℂ) (α δ : ℝ) : Matrix b a ℂ :=
  (-2 * Complex.I * (Real.sqrt (nu δ) : ℂ) / (α : ℂ)) •
    (L * (1 + (nu δ : ℂ) • gram L α)⁻¹)

def localChannel {a : Type} [Fintype a] [DecidableEq a]
    (L : Op a) (α δ : ℝ) (X : Op a) : Op a :=
  K0 L α δ * X * (K0 L α δ)ᴴ + K1 L α δ * X * (K1 L α δ)ᴴ

/-- Hermitian dilation, Eq. (36), with distinct domain and codomain copies. -/
def dilation {a b : Type} [Fintype a] [Fintype b]
    (L : Matrix b a ℂ) : Op (Sum a b) := Matrix.fromBlocks 0 Lᴴ L 0

def cayley {a : Type} [Fintype a] [DecidableEq a] (A : Op a) : Op a :=
  (1 - Complex.I • A) * (1 + Complex.I • A)⁻¹

def realCayley {a : Type} [Fintype a] [DecidableEq a] (A : Op a) : Op a :=
  (1 - A) * (1 + A)⁻¹

def inj0 {a b : Type} [DecidableEq a] : Matrix (Sum a b) a ℂ :=
  fun x y => match x with | .inl z => if z = y then 1 else 0 | .inr _ => 0

def inj1 {a b : Type} [DecidableEq b] : Matrix (Sum a b) b ℂ :=
  fun x y => match x with | .inl _ => 0 | .inr z => if z = y then 1 else 0

/-- Eq. (39); the input oracle is not required to be Hermitian. -/
def oracleLift {e : Type} [Fintype e] (O : Op e) : Op (Sum e e) := dilation O

def V0 {a e : Type} [DecidableEq e] [Fintype e] (Bin : Matrix e a ℂ) :
    Matrix (Sum e e) a ℂ := inj0 * Bin

def V1 {b e : Type} [DecidableEq e] [Fintype e] (Bout : Matrix e b ℂ) :
    Matrix (Sum e e) b ℂ := inj1 * Bout

/-- Eq. (46), including the norm-one jump-input transition. -/
def rotation {a b e : Type} [Fintype a] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq e]
    (Bin : Matrix e a ℂ) (Bout : Matrix e b ℂ) (δ : ℝ) :
    Op (Sum (Sum a b) (Sum e e)) :=
  let E0 := V0 Bin
  let E1 := V1 Bout
  let P0 := E0 * E0ᴴ
  let P1 := E1 * E1ᴴ
  Matrix.fromBlocks
    (Matrix.fromBlocks ((Real.sqrt (1-δ) : ℂ) • 1) 0 0 0)
    (Matrix.fromRows ((-Complex.I * (Real.sqrt δ : ℂ)) • E0ᴴ) (-Complex.I • E1ᴴ))
    (Matrix.fromCols ((Real.sqrt δ : ℂ) • E0) E1)
    (Complex.I • ((Real.sqrt (1-δ) : ℂ) • P0 + 1 - P0 - P1))

/-- Eqs. (43)--(45), computed without any catalyst-state oracle. -/
def catalyst {a b e : Type} [Fintype a] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq e]
    (L : Matrix b a ℂ) (α δ : ℝ) (O : Op e)
    (Bin : Matrix e a ℂ) (Bout : Matrix e b ℂ) : Matrix (Sum e e) a ℂ :=
  let y : Op a := (Real.sqrt δ : ℂ) •
    (1 + (Real.sqrt (1-δ) : ℂ) • realCayley (gram L α))⁻¹
  let M : Op (Sum a b) := 1 + Complex.I • ((α : ℂ)⁻¹ • dilation L)
  let z : Matrix (Sum a b) a ℂ := M⁻¹ * (inj0 : Matrix (Sum a b) a ℂ) * y
  let E := Matrix.fromCols (V0 Bin) (V1 Bout)
  (1 + Complex.I • oracleLift O) * E * z

/-- Exact normalized rectangular access data, as used by the local construction. -/
def exactAccess {a b e : Type} [Fintype a] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq e]
    (L : Matrix b a ℂ) (α : ℝ) (O : Op e)
    (Bin : Matrix e a ℂ) (Bout : Matrix e b ℂ) : Prop :=
  0 < α ∧ unitary O ∧ Binᴴ * Bin = 1 ∧ Boutᴴ * Bout = 1 ∧
    Boutᴴ * O * Bin = (α : ℂ)⁻¹ • L

end LindbladQueryOptimal.Simulation


