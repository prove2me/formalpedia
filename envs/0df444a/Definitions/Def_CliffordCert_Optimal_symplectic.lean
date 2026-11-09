-- Prove2me | Definitions.Def_CliffordCert_Optimal_symplectic
-- name    : CliffordCert_Optimal_symplectic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:29:10.226358+00:00
-- url     : https://prove2.me/theorems/0b91483c-fe8c-470b-9ab4-05f1e7c0de5b
-- title:
--   Binary symplectic geometry and verified finite preprocessing
-- statement:
--   Let $\mathbb F_2=\mathbb Z/2\mathbb Z$ and $V=\mathbb F_2^N$. A bilinear form $B$ is symplectic when it is alternating, $B(v,v)=0$, and nondegenerate. For a subspace $W$, put
--   $$W^\perp=\{v:B(v,w)=0\text{ for all }w\in W\},\qquad \operatorname{rad}(W)=W\cap W^\perp.$$
--   The definitions distinguish ordinary covers, nondegenerate covers, totally isotropic subspaces and paired bases. The repair cost is $f(0)=1$ and $f(t)=2^{\lfloor t/2\rfloor}+1$ for $t>0$; theorem uses have even $t$.
--
--   Finite preprocessing enumerates invertible coordinate changes, accepts $g$ exactly when $F(g)=\sum_W f(\dim\operatorname{rad}(gW))\le3L_0$, and exhaustively searches lists of at most $f(t)$ ambient subspaces for each repair. Search returns an option and may fail on invalid inputs; success is a theorem conclusion. The first accepted trial of an infinite GL sequence defines an extended-natural stopping count, with infinity for nontermination. Independent uniform finite GL words define its actual stopping tails, and the extended nonnegative tail sum defines expected trials. It cannot silently assign zero to a divergent expectation. The module also defines the uniform Grassmannian average and the finite-field lines of Eq. (21).
--
--   These objects supply the reusable finite geometry layer. Enumeration orders are arbitrary but finite and exhaustive; no efficiency bound is encoded.
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 10, §B.1, Eq. (16); pp. 11–14, §§B–C (PDF pp. 12–15) (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Mathlib
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal ENat

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq
abbrev F₂ := ZMod 2
abbrev Binary (N : ℕ) := Fin N → F₂
abbrev Form (N : ℕ) := Binary N →ₗ[F₂] Binary N →ₗ[F₂] F₂

def IsSymplectic {N : ℕ} (B : Form N) : Prop :=
  (∀ v, B v v = 0) ∧ (∀ v, (∀ w, B v w = 0) → v = 0)

def perpendicular {N : ℕ} (B : Form N) (W : Submodule F₂ (Binary N)) :
    Submodule F₂ (Binary N) where
  carrier := {v | ∀ w ∈ W, B v w = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy w hw; simp [hx w hw, hy w hw]
  smul_mem' := by intro a x hx w hw; simp [hx w hw]

def radical {N : ℕ} (B : Form N) (W : Submodule F₂ (Binary N)) :=
  W ⊓ perpendicular B W

def Nondegenerate {N : ℕ} (B : Form N) (W : Submodule F₂ (Binary N)) : Prop :=
  radical B W = ⊥

def IsIsotropic {N : ℕ} (B : Form N) (W : Submodule F₂ (Binary N)) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, B v w = 0

def Covers {N : ℕ} (W : List (Submodule F₂ (Binary N)))
    (A : Submodule F₂ (Binary N)) : Prop := ∀ v ∈ A, ∃ S ∈ W, v ∈ S

def IsKCover {N : ℕ} (k : ℕ) (W : List (Submodule F₂ (Binary N))) : Prop :=
  Covers W ⊤ ∧ ∀ S ∈ W, Module.finrank F₂ S = k

def IsGoodCover {N : ℕ} (B : Form N) (k : ℕ)
    (W : List (Submodule F₂ (Binary N))) : Prop :=
  IsKCover k W ∧ ∀ S ∈ W, Nondegenerate B S

def Paired {N h : ℕ} (B : Form N) (b : (Fin h ⊕ Fin h) → Binary N) : Prop :=
  (∀ i j, B (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) ∧
  (∀ i j, B (b (.inl i)) (b (.inl j)) = 0) ∧
  (∀ i j, B (b (.inr i)) (b (.inr j)) = 0)

def repairCost (t : ℕ) : ℕ := if t = 0 then 1 else 2 ^ (t / 2) + 1

def repairOptions {N : ℕ} (B : Form N) (W : Submodule F₂ (Binary N)) :
    List (List (Submodule F₂ (Binary N))) :=
  letI := Fintype.ofFinite (Submodule F₂ (Binary N))
  (List.finRange (repairCost (Module.finrank F₂ (radical B W)) + 1)).flatMap fun l =>
    (Finset.univ : Finset (Fin l.val → Submodule F₂ (Binary N))).toList.map
      (fun f => List.ofFn f)

def repairCheck {N : ℕ} (B : Form N) (W : Submodule F₂ (Binary N))
    (S : List (Submodule F₂ (Binary N))) : Prop :=
  Covers S W ∧ ∀ U ∈ S, Module.finrank F₂ U = Module.finrank F₂ W ∧ Nondegenerate B U

def repairSearch {N : ℕ} (B : Form N) (W : Submodule F₂ (Binary N)) :
    Option (List (Submodule F₂ (Binary N))) :=
  (repairOptions B W).find? (fun S => decide (repairCheck B W S))

abbrev Coordinates (N : ℕ) := Binary N ≃ₗ[F₂] Binary N

instance coordinatesFintype (N : ℕ) : Fintype (Coordinates N) :=
  Fintype.ofInjective (fun g : Coordinates N => (g : Binary N → Binary N))
    (by intro a b h; exact LinearEquiv.ext (congrFun h))

def coordinateList (N : ℕ) : List (Coordinates N) :=
  (Finset.univ : Finset (Coordinates N)).toList

def totalRepairCost {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N)))
    (g : Coordinates N) : ℕ :=
  ((W.map fun U => repairCost (Module.finrank F₂ (radical B (U.map g.toLinearMap))))).sum

def coordinateCheck {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N)))
    (g : Coordinates N) : Prop := totalRepairCost B W g ≤ 3 * W.length

def deterministicCoordinate {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N))) :
    Option (Coordinates N) :=
  (coordinateList N).find? (fun g => decide (coordinateCheck B W g))

def repairedOutput {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N)))
    (g : Coordinates N) : Option (List (Submodule F₂ (Binary N))) :=
  (W.mapM fun U => repairSearch B (U.map g.toLinearMap)).map List.flatten

/-- Uniform independent finite prefixes of GL trials, with the first successful trial.
    Infinite tails are specified by all finite-prefix probabilities below. -/
def firstAccepted {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N)))
    (trials : List (Coordinates N)) : Option (Coordinates N) :=
  trials.find? (fun g => decide (coordinateCheck B W g))

/-- Actual stopping count on an infinite sequence of GL trials; infinity means no success. -/
def stoppingTrial {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N)))
    (gs : ℕ → Coordinates N) : ℕ∞ :=
  if h : ∃ j, coordinateCheck B W (gs j) then ((Nat.find h + 1 : ℕ) : ℕ∞) else ⊤

def stoppedOutput {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N)))
    (gs : ℕ → Coordinates N) : Option (List (Submodule F₂ (Binary N))) :=
  if h : ∃ j, coordinateCheck B W (gs j) then repairedOutput B W (gs (Nat.find h)) else none

def trialTail {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N))) (j : ℕ) : ℝ :=
  let rejected := (Finset.univ : Finset (Fin j → Coordinates N)).filter
    (fun gs => ∀ i, ¬ coordinateCheck B W (gs i))
  (rejected.card : ℝ) / (Fintype.card (Fin j → Coordinates N) : ℝ)

/-- Tail-sum expectation, extended-valued so nontermination cannot become zero. -/
def expectedTrials {N : ℕ} (B : Form N) (W : List (Submodule F₂ (Binary N))) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (trialTail B W j)

def grassmannian (N k : ℕ) : Finset (Submodule F₂ (Binary N)) :=
  letI := Fintype.ofFinite (Submodule F₂ (Binary N))
  Finset.univ.filter (fun W => Module.finrank F₂ W = k)

def expectedRadical {N : ℕ} (B : Form N) (k : ℕ) : ℝ :=
  (∑ W ∈ grassmannian N k, (Nat.card (radical B W) : ℝ)) /
    (grassmannian N k).card

abbrev SpreadField (a : ℕ) := GaloisField 2 a

def spreadLine (a : ℕ) (b : Option (SpreadField a)) :
    Submodule F₂ (SpreadField a × SpreadField a) where
  carrier := match b with
    | none => {z | z.1 = 0}
    | some c => {z | z.2 = c * z.1}
  zero_mem' := by cases b <;> simp
  add_mem' := by cases b <;> simp_all [mul_add]
  smul_mem' := by cases b <;> simp_all [Algebra.smul_def, mul_left_comm]
end CliffordCert.Optimal


