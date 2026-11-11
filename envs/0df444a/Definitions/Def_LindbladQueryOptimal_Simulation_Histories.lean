-- Prove2me | Definitions.Def_LindbladQueryOptimal_Simulation_Histories
-- name    : LindbladQueryOptimal_Simulation_Histories
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:23.552393+00:00
-- url     : https://prove2.me/theorems/1ab91cad-4b5a-4fa0-898a-285538aaa636
-- title:
--   Chronological history rotations and independent private-path kernels
-- statement:
--   A history has one no-jump or jump symbol per time. Local rotations are embedded into the public history register and their own time-labeled private sector, with identity on every other coordinate. Their product is taken in chronological order. Valid private coordinates at time $\ell$ have every history entry from $\ell$ onward equal to zero.
--
--   For the single-jump construction, the two correction kernels are defined directly from Eqs. (76)–(77), independently of the global private block. A regular transition has diagonal amplitude $1-\sqrt{1-\delta}$ or off-diagonal amplitude $\delta(\sqrt{1-\delta})^{k-\ell-1}$. A jump transition has amplitude $\sqrt\delta(\sqrt{1-\delta})^{k-\ell-1}$ and records one jump at the departure time. History-preserving contractions and the ordered words of Eq. (82) use these kernels. The cancellation polynomial is
--   $$p_{\rm annih}(A)=\tfrac12(A^2+A^4).$$
--   The full private coordinates are retained in the chronological rotation; polynomial norms use its restriction to the valid coordinate subtype. This file does not supply the stacked multi-oracle construction, combined Hamiltonian stages, reuse circuits, or a gate compiler.
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), §§3.2–3.4, pp. 17–23, Eqs. (65)–(87); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev History (r m : ℕ) := Fin r → Fin (m+1)
abbrev Public (r m : ℕ) (a : Type) := History r m × a
abbrev Private (r m : ℕ) (e : Type) := Fin r × History r m × e
abbrev Total (r m : ℕ) (a e : Type) := Sum (Public r m a) (Private r m e)
abbrev LocalPublic (m : ℕ) (a : Type) := Sum a (Fin m × a)

/-- The valid private coordinates of Eqs. (72), (121), with future history zero. -/
def valid {r m : ℕ} {e : Type} (x : Private r m e) : Prop :=
  ∀ k : Fin r, x.1 ≤ k → x.2.1 k = 0

abbrev Valid (r m : ℕ) (e : Type) := {x : Private r m e // valid x}

/-- Literal coordinate embedding of a local rotation into a time/history sector. -/
def localPosition {r m : ℕ} {a e : Type} (j : Fin r) (h : History r m) :
    Sum (LocalPublic m a) e → Total r m a e
  | .inl (.inl x) => .inl (h,x)
  | .inl (.inr (k,x)) => .inl (Function.update h j ⟨k.val+1, Nat.succ_lt_succ k.isLt⟩,x)
  | .inr x => .inr (j,h,x)

def localEmbedding {r m : ℕ} {a e : Type} (j : Fin r) (h : History r m) :
    Matrix (Total r m a e) (Sum (LocalPublic m a) e) ℂ :=
  fun x y => if x = localPosition j h y then 1 else 0

/-- Eq. (66), including identity on all unvisited sectors. -/
def liftedRotation {r m : ℕ} {a e : Type} [Fintype a] [Fintype e]
    (R : Op (Sum (LocalPublic m a) e)) (j : Fin r) : Op (Total r m a e) :=
  let active := fun h : History r m => ∀ k : Fin r, j ≤ k → h k = 0
  (∑ h : History r m, if active h then
    (localEmbedding (a := a) (e := e) j h) * R * (localEmbedding (a := a) (e := e) j h)ᴴ else 0) +
  (1 - ∑ h : History r m, if active h then
    (localEmbedding (a := a) (e := e) j h) * (localEmbedding (a := a) (e := e) j h)ᴴ else 0)

/-- Chronological query-free product, Eqs. (68), (116). -/
def globalRotation {r m : ℕ} {a e : Type} [Fintype a] [Fintype e]
    (R : Op (Sum (LocalPublic m a) e)) : Op (Total r m a e) :=
  (List.ofFn (liftedRotation (r := r) R)).foldl (fun acc U => U * acc) 1

def globalOracle {r m : ℕ} {e : Type} (O : Op e) : Op (Private r m e) :=
  fun x y => if x.1 = y.1 ∧ x.2.1 = y.2.1 then O x.2.2 y.2.2 else 0

def restrictedOracle {r m : ℕ} {e : Type} (O : Op e) : Op (Valid r m e) :=
  fun x y => globalOracle O x.val y.val

def privateRotation {r m : ℕ} {a e : Type} [Fintype a] [Fintype e]
    (R : Op (Sum (LocalPublic m a) e)) : Op (Valid r m e) :=
  fun x y => globalRotation (r := r) R (.inr x.val) (.inr y.val)

def jumpProjection {r m : ℕ} {e : Type} (P : Op e) : Op (Valid r m e) :=
  fun x y => if x.val.1 = y.val.1 ∧ x.val.2.1 = y.val.2.1 then
    P x.val.2.2 y.val.2.2 else 0

def timeBlock {r m : ℕ} {e : Type} (i j : Fin r) (A : Op (Valid r m e)) :
    Op (Valid r m e) :=
  fun x y => if x.val.1 = i ∧ y.val.1 = j then A x y else 0

def historyPreserving {r m : ℕ} {e : Type} (D : Op (Valid r m e)) : Prop :=
  ∀ x y, D x y ≠ 0 → x.val.1 = y.val.1 ∧ x.val.2.1 = y.val.2.1

def annihilate {e : Type} [Fintype e] [DecidableEq e] (A : Op e) : Op e :=
  (1/2 : ℂ) • (A^2 + A^4)

/-- Single-jump branch identification, since Fin 1 × a is a copy of a. -/
def singleIdentification {a e : Type} :
    Matrix (Sum (LocalPublic 1 a) e) (Sum (Sum a a) e) ℂ :=
  fun x y => if x = (match y with
    | .inl (.inl z) => .inl (.inl z)
    | .inl (.inr z) => .inl (.inr (0,z))
    | .inr z => .inr z) then 1 else 0

def singleRotation {a e : Type} [Fintype a] [Fintype e]
    (Bin Bout : Matrix e a ℂ) (δ : ℝ) :
    Op (Sum (LocalPublic 1 a) (Sum e e)) :=
  (singleIdentification (a := a) (e := Sum e e)) * rotation Bin Bout δ *
    (singleIdentification (a := a) (e := Sum e e))ᴴ

def singleP {a e : Type} [Fintype a] [Fintype e] (Bout : Matrix e a ℂ) : Op (Sum e e) :=
  V1 Bout * (V1 Bout)ᴴ

/-- Input and output history equality after a single jump at the departure time. -/
def addsJump {r m : ℕ} (i j : Fin r) (hout hin : History r m) : Prop :=
  j < i ∧ hout j ≠ 0 ∧ ∀ k : Fin r, k ≠ j → hout k = hin k

/-- Eq. (76), defined directly by chronological path amplitudes. -/
def singleDeltaR {r : ℕ} {a e : Type} [Fintype a] [Fintype e]
    (Bin : Matrix e a ℂ) (δ : ℝ) : Op (Valid r 1 (Sum e e)) :=
  let P0 := V0 Bin * (V0 Bin)ᴴ
  fun x y => if x.val.2.1 = y.val.2.1 then
    if x.val.1 = y.val.1 then
      (1 - Real.sqrt (1-δ)) * P0 x.val.2.2 y.val.2.2
    else if y.val.1 < x.val.1 then
      (δ * Real.sqrt (1-δ)^(x.val.1.val-y.val.1.val-1) : ℝ) * P0 x.val.2.2 y.val.2.2
    else 0
  else 0

/-- Eq. (77), with exactly one recorded jump at the departure time. -/
def singleDeltaJ {r : ℕ} {a e : Type} [Fintype a] [Fintype e]
    (Bin Bout : Matrix e a ℂ) (δ : ℝ) : Op (Valid r 1 (Sum e e)) :=
  let Q := V0 Bin * (V1 Bout)ᴴ
  fun x y => if addsJump x.val.1 y.val.1 x.val.2.1 y.val.2.1 then
    (Real.sqrt δ * Real.sqrt (1-δ)^(x.val.1.val-y.val.1.val-1) : ℝ) * Q x.val.2.2 y.val.2.2
  else 0

/-- Eq. (82), using the independent kernels (76)--(77). -/
def singleWord {r : ℕ} {a e : Type} [Fintype a] [Fintype e]
    (Bin Bout : Matrix e a ℂ) (δ : ℝ) (σ : List Bool)
    (D : ℕ → Op (Valid r 1 (Sum e e))) : Op (Valid r 1 (Sum e e)) :=
  (σ.zipIdx).foldl (fun A s =>
    D (s.2+1) * (if s.1 then singleDeltaJ Bin Bout δ else singleDeltaR Bin δ) * A) (D 0)

end LindbladQueryOptimal.Simulation


