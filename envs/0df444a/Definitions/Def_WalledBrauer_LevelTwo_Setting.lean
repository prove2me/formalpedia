-- Prove2me | Definitions.Def_WalledBrauer_LevelTwo_Setting
-- name    : WalledBrauer_LevelTwo_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:17.155254+00:00
-- url     : https://prove2.me/theorems/cb0f4386-1fca-4d05-9b56-990760923833
-- title:
--   The walled Brauer and level-two cyclotomic algebras and the truncation
-- statement:
--   Fix nonnegative integers $r,t$. An orientation is a word of length $r+t$ with exactly $r$ upward arrows. The **walled Brauer algebra** $\operatorname{Br}_{r,t}(d)$ over $\mathbb C$ is the algebra with the orientation idempotents and the crossing and contraction generators of Definition 2.1, subject to (Br1)–(Br6). A generator with an inadmissible local orientation is zero. Each dotted relation is imposed for each pair of composable oriented words with the same source and target.
--
--   Fix positive integers $m,n$ and an integer $\delta$. The **level-two cyclotomic algebra** $A=\mathbb V\operatorname{Br}^{\mathrm{cycl}}_{r,t}$ has the degenerate affine generators $y_j$ and the relations of Definitions 2.5 and 2.8. Its parameters are those of (5.4):
--   $$\beta^\uparrow_1=-\delta+(m+n)/2,\quad \beta^\uparrow_2=(n-m)/2,\quad \beta^\downarrow_1=(m+n)/2,\quad \beta^\downarrow_2=\delta+(m-n)/2,$$
--   $$\omega_0=m+n,\qquad\omega_1=-\delta m+(m+n)^2/2,\qquad\omega_{j+2}=(\beta^\uparrow_1+\beta^\uparrow_2)\omega_{j+1}-\beta^\uparrow_1\beta^\uparrow_2\omega_j.$$
--
--   The spectral idempotent $\eta_j1_a$ is selected by its polynomial, idempotence, generalized-eigenspace, and corner-invertibility properties. Set $f_k1_a=\eta_1\cdots\eta_k1_a$, $f1_a=f_{r+t}1_a$, and $f=\sum_a f1_a$. The elements $b_j,c_j$, the inverse in an idempotent corner, and the images $\sigma_j,\widehat\sigma_j,\tau_j,\widehat\tau_j$ are the elements of (6.1)–(6.4).
--
--   This presentation is the common setting for the mission's isomorphism and its supporting identities. **Formalization Note** Positions start at zero in Lean. A family of polynomial square roots is specified separately in each theorem, allowing every choice the paper permits. The corrected mixed-orientation reading of (Br3) in Definition 2.5 is used.
-- source:
--   Sartori and Stroppel, Walled Brauer algebras as idempotent truncations of level 2 cyclotomic quotients, arXiv:1411.2771v2, pp. 3–4, Definition 2.1; pp. 5–6, Definitions 2.5 and 2.8; p. 10, (5.4); p. 12, Definition 5.6; p. 13, (6.1)–(6.4)

import Mathlib

namespace WalledBrauer.LevelTwo

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Orientations have exactly `r` upward arrows. Positions are zero based. -/
abbrev Orientation (r t : ℕ) := {a : Fin (r + t) → Bool //
  (Finset.univ.filter (fun i => a i = true)).card = r}

/-- The adjacent transposition of an orientation. -/
def swapOrientation {r t : ℕ} (a : Orientation r t) (k : Fin (r + t))
    (h : k.val + 1 < r + t) : Orientation r t :=
  ⟨fun i => a.1 (Equiv.swap k ⟨k.val + 1, h⟩ i), by
    have he := (Equiv.swap k ⟨k.val + 1, h⟩).sum_comp Finset.univ
      (fun i : Fin (r + t) => if a.1 i = true then (1 : ℕ) else 0)
    have he' := he (by simp)
    have ha : (∑ i : Fin (r + t), if a.1 i = true then (1 : ℕ) else 0) = r := by
      simpa only [Finset.card_filter] using a.2
    simpa only [Finset.card_filter] using he'.trans ha⟩

inductive Kind where
  | idem | s | sh | e | eh | y
  deriving DecidableEq

structure Gen (r t : ℕ) where
  kind : Kind
  pos : Fin (r + t)
  source : Orientation r t
  deriving DecidableEq

abbrev Free (r t : ℕ) := FreeAlgebra ℂ (Gen r t)

def atom {r t : ℕ} (kind : Kind) (k : Fin (r + t)) (a : Orientation r t) : Free r t :=
  FreeAlgebra.ι ℂ ⟨kind, k, a⟩

def id {r t : ℕ} (a : Orientation r t) : Free r t :=
  if h : 0 < r + t then atom .idem ⟨0, h⟩ a else 1

def next {r t : ℕ} (k : Fin (r + t)) (h : k.val + 1 < r + t) : Fin (r + t) :=
  ⟨k.val + 1, h⟩

def adjacent {r t : ℕ} (a : Orientation r t) (k : Fin (r + t)) : Prop :=
  ∃ h : k.val + 1 < r + t, a.1 k = a.1 (next k h)

def opposite {r t : ℕ} (a : Orientation r t) (k : Fin (r + t)) : Prop :=
  ∃ h : k.val + 1 < r + t, a.1 k ≠ a.1 (next k h)

def target {r t : ℕ} (kind : Kind) (k : Fin (r + t)) (a : Orientation r t) :
    Orientation r t :=
  if h : k.val + 1 < r + t then
    if kind = .sh ∨ kind = .eh then swapOrientation a k h else a
  else a

def allowed {r t : ℕ} (kind : Kind) (k : Fin (r + t)) (a : Orientation r t) : Prop :=
  match kind with
  | .idem | .y => True
  | .s => adjacent a k
  | .sh | .e | .eh => opposite a k

structure Step (r t : ℕ) where
  kind : Kind
  pos : Fin (r + t)

def wordTarget {r t : ℕ} : List (Step r t) → Orientation r t → Orientation r t
  | [], a => a
  | x :: xs, a => target x.kind x.pos (wordTarget xs a)

def wordValid {r t : ℕ} : List (Step r t) → Orientation r t → Prop
  | [], _ => True
  | x :: xs, a => wordValid xs a ∧ allowed x.kind x.pos (wordTarget xs a)

def word {r t : ℕ} : List (Step r t) → Orientation r t → Free r t
  | [], a => id a
  | x :: xs, a => atom x.kind x.pos (wordTarget xs a) * word xs a

def dottedS (hat : Bool) : Kind := if hat then .sh else .s
def dottedE (hat : Bool) : Kind := if hat then .eh else .e
def step {r t : ℕ} (kind : Kind) (k : Fin (r + t)) : Step r t := ⟨kind, k⟩

def total {r t : ℕ} (kind : Kind) (k : Fin (r + t)) : Free r t :=
  ∑ a : Orientation r t, atom kind k a

/-- The local version of a dotted relation: both words must be composable from
the same source to the same target. -/
def Comparable {r t : ℕ} (xs ys : List (Step r t)) (a : Orientation r t) : Prop :=
  wordValid xs a ∧ wordValid ys a ∧ wordTarget xs a = wordTarget ys a

/-- Defs. 2.1, 2.5, 2.8. The `affine` flag adds the y relations; `cycl` adds
the two level-two relations. In the non-affine presentation the y symbols vanish. -/
inductive Relations (r t : ℕ) (d : ℂ) (ω : ℕ → ℂ)
    (β1 β2 : Bool → ℂ) (affine cycl : Bool) : Free r t → Free r t → Prop where
  | complete : Relations r t d ω β1 β2 affine cycl
      (∑ a : Orientation r t, id a) 1
  | orthogonal (a b : Orientation r t) : Relations r t d ω β1 β2 affine cycl
      (id a * id b) (if a = b then id a else 0)
  | source (z : Kind) (k : Fin (r + t)) (a : Orientation r t) :
      Relations r t d ω β1 β2 affine cycl (atom z k a * id a) (atom z k a)
  | dest (z : Kind) (k : Fin (r + t)) (a : Orientation r t) :
      Relations r t d ω β1 β2 affine cycl
        (id (target z k a) * atom z k a) (atom z k a)
  | invalid (z : Kind) (k : Fin (r + t)) (a : Orientation r t)
      (h : ¬ allowed z k a) : Relations r t d ω β1 β2 affine cycl (atom z k a) 0
  | idem_pos (k : Fin (r + t)) (a : Orientation r t) :
      Relations r t d ω β1 β2 affine cycl (atom .idem k a) (id a)
  | br3 (k : Fin (r + t)) (a : Orientation r t) (hk : k.val + 1 < r + t) :
      Relations r t d ω β1 β2 affine cycl
        ((total .s k ^ 2 + total .sh k ^ 2) * id a) (id a)
  | br4a (k j : Fin (r + t)) (hfar : k.val + 1 < j.val ∨ j.val + 1 < k.val)
      (u v : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedS u) k, step (dottedS v) j]
        [step (dottedS v) j, step (dottedS u) k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedS u) k, step (dottedS v) j] a)
        (word [step (dottedS v) j, step (dottedS u) k] a)
  | br4b (k : Fin (r + t)) (hk : k.val + 2 < r + t)
      (u v w u' v' w' : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedS u) k, step (dottedS v) ⟨k.val+1, by omega⟩,
          step (dottedS w) k]
        [step (dottedS u') ⟨k.val+1, by omega⟩, step (dottedS v') k,
          step (dottedS w') ⟨k.val+1, by omega⟩] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedS u) k, step (dottedS v) ⟨k.val+1, by omega⟩,
          step (dottedS w) k] a)
        (word [step (dottedS u') ⟨k.val+1, by omega⟩, step (dottedS v') k,
          step (dottedS w') ⟨k.val+1, by omega⟩] a)
  | br5 (k : Fin (r + t)) (hk : k.val + 1 < r + t) :
      Relations r t d ω β1 β2 affine cycl (total .e k ^ 2)
        (algebraMap ℂ (Free r t) d * total .e k)
  | br6aS (k j : Fin (r + t)) (hfar : k.val + 1 < j.val ∨ j.val + 1 < k.val)
      (u v : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedS u) k, step (dottedE v) j]
        [step (dottedE v) j, step (dottedS u) k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedS u) k, step (dottedE v) j] a)
        (word [step (dottedE v) j, step (dottedS u) k] a)
  | br6aE (k j : Fin (r + t)) (hfar : k.val + 1 < j.val ∨ j.val + 1 < k.val)
      (u v : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedE u) k, step (dottedE v) j]
        [step (dottedE v) j, step (dottedE u) k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedE u) k, step (dottedE v) j] a)
        (word [step (dottedE v) j, step (dottedE u) k] a)
  | br6bL (k : Fin (r + t)) (u v : Bool) (a : Orientation r t)
      (h : Comparable [step .sh k, step (dottedE u) k] [step (dottedE v) k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step .sh k, step (dottedE u) k] a) (word [step (dottedE v) k] a)
  | br6bR (k : Fin (r + t)) (u v : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedE u) k, step .sh k] [step (dottedE v) k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedE u) k, step .sh k] a) (word [step (dottedE v) k] a)
  | br6c1 (k : Fin (r + t)) (hk : k.val + 2 < r + t)
      (u v w u' v' : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedS u) k, step (dottedE v) ⟨k.val+1, by omega⟩,
          step (dottedE w) k]
        [step (dottedS u') ⟨k.val+1, by omega⟩, step (dottedE v') k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedS u) k, step (dottedE v) ⟨k.val+1, by omega⟩,
          step (dottedE w) k] a)
        (word [step (dottedS u') ⟨k.val+1, by omega⟩, step (dottedE v') k] a)
  | br6c2 (k : Fin (r + t)) (hk : k.val + 2 < r + t)
      (u v w u' v' : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedE u) k, step (dottedE v) ⟨k.val+1, by omega⟩,
          step (dottedS w) k]
        [step (dottedE u') k, step (dottedS v') ⟨k.val+1, by omega⟩] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedE u) k, step (dottedE v) ⟨k.val+1, by omega⟩,
          step (dottedS w) k] a)
        (word [step (dottedE u') k, step (dottedS v') ⟨k.val+1, by omega⟩] a)
  | br6c3 (k : Fin (r + t)) (hk : k.val + 2 < r + t)
      (u v w u' v' : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedE u) ⟨k.val+1, by omega⟩,
          step (dottedE v) k, step (dottedS w) ⟨k.val+1, by omega⟩]
        [step (dottedE u') ⟨k.val+1, by omega⟩, step (dottedS v') k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedE u) ⟨k.val+1, by omega⟩,
          step (dottedE v) k, step (dottedS w) ⟨k.val+1, by omega⟩] a)
        (word [step (dottedE u') ⟨k.val+1, by omega⟩, step (dottedS v') k] a)
  | br6c4 (k : Fin (r + t)) (hk : k.val + 2 < r + t)
      (u v w u' v' : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedS u) ⟨k.val+1, by omega⟩,
          step (dottedE v) k, step (dottedE w) ⟨k.val+1, by omega⟩]
        [step (dottedS u') k, step (dottedE v') ⟨k.val+1, by omega⟩] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedS u) ⟨k.val+1, by omega⟩,
          step (dottedE v) k, step (dottedE w) ⟨k.val+1, by omega⟩] a)
        (word [step (dottedS u') k, step (dottedE v') ⟨k.val+1, by omega⟩] a)
  | br6d1 (k : Fin (r + t)) (hk : k.val + 2 < r + t)
      (u v w u' : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedE u) ⟨k.val+1, by omega⟩,
          step (dottedE v) k, step (dottedE w) ⟨k.val+1, by omega⟩]
        [step (dottedE u') ⟨k.val+1, by omega⟩] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedE u) ⟨k.val+1, by omega⟩,
          step (dottedE v) k, step (dottedE w) ⟨k.val+1, by omega⟩] a)
        (word [step (dottedE u') ⟨k.val+1, by omega⟩] a)
  | br6d2 (k : Fin (r + t)) (hk : k.val + 2 < r + t)
      (u v w u' : Bool) (a : Orientation r t)
      (h : Comparable [step (dottedE u) k,
          step (dottedE v) ⟨k.val+1, by omega⟩, step (dottedE w) k]
        [step (dottedE u') k] a) :
      Relations r t d ω β1 β2 affine cycl
        (word [step (dottedE u) k,
          step (dottedE v) ⟨k.val+1, by omega⟩, step (dottedE w) k] a)
        (word [step (dottedE u') k] a)
  | no_y (k : Fin (r + t)) (a : Orientation r t) (h : affine = false) :
      Relations r t d ω β1 β2 affine cycl (atom .y k a) 0
  | a1 (i j : Fin (r + t)) (a b : Orientation r t) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        (total .y i * total .y j) (total .y j * total .y i)
  | a2s (i k : Fin (r + t)) (hfar : i ≠ k)
      (hnext : ∀ h : k.val + 1 < r + t, i ≠ next k h)
      (u : Bool) (a : Orientation r t) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        (total (dottedS u) k * total .y i) (total .y i * total (dottedS u) k)
  | a2e (i k : Fin (r + t)) (hfar : i ≠ k)
      (hnext : ∀ h : k.val + 1 < r + t, i ≠ next k h)
      (u : Bool) (a : Orientation r t) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        (total (dottedE u) k * total .y i) (total .y i * total (dottedE u) k)
  | a3 (a : Orientation r t) (j : ℕ) (h : affine = true)
      (hN : 1 < r + t) (ha : a.1 ⟨0, by omega⟩ = true ∧ a.1 ⟨1, by omega⟩ = false) :
      Relations r t d ω β1 β2 affine cycl
        (total .e ⟨0, by omega⟩ * total .y ⟨0, by omega⟩ ^ j *
          total .e ⟨0, by omega⟩ * id a)
        (algebraMap ℂ (Free r t) (ω j) * total .e ⟨0, by omega⟩ * id a)
  | a4s1 (k : Fin (r + t)) (hk : k.val + 1 < r + t)
      (a : Orientation r t) (ha : adjacent a k) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        ((total .s k * total .y k - total .y (next k hk) * total .s k) * id a)
        (-id a)
  | a4s2 (k : Fin (r + t)) (hk : k.val + 1 < r + t)
      (a : Orientation r t) (ha : adjacent a k) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        ((total .s k * total .y (next k hk) - total .y k * total .s k) * id a)
        (id a)
  | a4h1 (k : Fin (r + t)) (hk : k.val + 1 < r + t) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        (total .sh k * total .y k - total .y (next k hk) * total .sh k)
        (total .eh k)
  | a4h2 (k : Fin (r + t)) (hk : k.val + 1 < r + t) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        (total .sh k * total .y (next k hk) - total .y k * total .sh k)
        (-total .eh k)
  | a5L (k : Fin (r + t)) (hk : k.val + 1 < r + t)
      (u : Bool) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        (total (dottedE u) k * (total .y k + total .y (next k hk))) 0
  | a5R (k : Fin (r + t)) (hk : k.val + 1 < r + t)
      (u : Bool) (h : affine = true) :
      Relations r t d ω β1 β2 affine cycl
        ((total .y k + total .y (next k hk)) * total (dottedE u) k) 0
  | cycl_relation (a : Orientation r t) (hN : 0 < r + t) (h : cycl = true) :
      Relations r t d ω β1 β2 affine cycl
        ((total .y ⟨0, hN⟩ - algebraMap ℂ (Free r t) (β1 (a.1 ⟨0, hN⟩))) *
         (total .y ⟨0, hN⟩ - algebraMap ℂ (Free r t) (β2 (a.1 ⟨0, hN⟩))) * id a) 0

abbrev Br (r t : ℕ) (d : ℂ) :=
  RingQuot (Relations r t d (fun _ => 0) (fun _ => 0) (fun _ => 0) false false)

def βone (m n : ℕ) (δ : ℤ) : Bool → ℂ
  | true => -(δ : ℂ) + ((m : ℂ) + (n : ℂ)) / 2
  | false => ((m : ℂ) + (n : ℂ)) / 2

def βtwo (m n : ℕ) (δ : ℤ) : Bool → ℂ
  | true => ((n : ℂ) - (m : ℂ)) / 2
  | false => (δ : ℂ) + ((m : ℂ) - (n : ℂ)) / 2

def omegaSeq (m n : ℕ) (δ : ℤ) : ℕ → ℂ
  | 0 => (m : ℂ) + (n : ℂ)
  | 1 => -(δ : ℂ) * (m : ℂ) + ((m : ℂ) + (n : ℂ)) ^ 2 / 2
  | j + 2 =>
      (βone m n δ true + βtwo m n δ true) * omegaSeq m n δ (j + 1) -
        βone m n δ true * βtwo m n δ true * omegaSeq m n δ j

abbrev A (r t m n : ℕ) (δ : ℤ) :=
  RingQuot (Relations r t (omegaSeq m n δ 0) (omegaSeq m n δ)
    (βone m n δ) (βtwo m n δ) true true)

def brAtom {r t : ℕ} (d : ℂ) (z : Kind) (k : Fin (r + t))
    (a : Orientation r t) : Br r t d :=
  RingQuot.mkAlgHom ℂ (Relations r t d (fun _ => 0) (fun _ => 0)
    (fun _ => 0) false false) (atom z k a)

def cyclAtom {r t m n : ℕ} (δ : ℤ) (z : Kind) (k : Fin (r + t))
    (a : Orientation r t) : A r t m n δ :=
  RingQuot.mkAlgHom ℂ (Relations r t (omegaSeq m n δ 0) (omegaSeq m n δ)
    (βone m n δ) (βtwo m n δ) true true) (atom z k a)

def brId {r t : ℕ} (d : ℂ) (a : Orientation r t) : Br r t d :=
  if h : 0 < r + t then brAtom d .idem ⟨0, h⟩ a else 1

def cyclId {r t m n : ℕ} (δ : ℤ) (a : Orientation r t) : A r t m n δ :=
  if h : 0 < r + t then cyclAtom δ .idem ⟨0, h⟩ a else 1

def cyclTotal {r t m n : ℕ} (δ : ℤ) (z : Kind) (k : Fin (r + t)) : A r t m n δ :=
  ∑ a : Orientation r t, cyclAtom δ z k a

def cyclY {r t m n : ℕ} (δ : ℤ) (k : Fin (r + t)) : A r t m n δ :=
  cyclTotal δ .y k

/-- The spectral idempotent excluding the `β₁` generalized eigenspace,
specified inside the polynomial algebra in `y_k 1_a`. -/
def EtaProperty {r t m n : ℕ} (δ : ℤ) (k : Fin (r + t))
    (a : Orientation r t) (e : A r t m n δ) : Prop :=
  let u := cyclId δ a
  let x := cyclY δ k - algebraMap ℂ (A r t m n δ) (βone m n δ (a.1 k))
  (∃ p : Polynomial ℂ, e = u * p.eval₂ (algebraMap ℂ (A r t m n δ)) (cyclY δ k)) ∧
  e * e = e ∧ u * e = e ∧ e * u = e ∧
  (∃ N : ℕ, x ^ N * (u - e) = 0) ∧
  (∃ g : A r t m n δ, g = e * g * e ∧ g * x * e = e ∧ x * e * g = e)

def eta {r t m n : ℕ} (δ : ℤ) (k : Fin (r + t))
    (a : Orientation r t) : A r t m n δ := by
  classical
  exact if h : ∃ e : A r t m n δ, EtaProperty δ k a e then Classical.choose h else 0

def fPrefix {r t m n : ℕ} (δ : ℤ) (a : Orientation r t) : ℕ → A r t m n δ
  | 0 => cyclId δ a
  | k + 1 => if h : k < r + t then fPrefix δ a k * eta δ ⟨k, h⟩ a
      else fPrefix δ a k

def fAt {r t m n : ℕ} (δ : ℤ) (a : Orientation r t) : A r t m n δ :=
  fPrefix δ a (r + t)

def fGlobalPrefix {r t m n : ℕ} (δ : ℤ) (k : ℕ) : A r t m n δ :=
  ∑ a : Orientation r t, fPrefix δ a k

def f {r t m n : ℕ} (δ : ℤ) : A r t m n δ :=
  ∑ a : Orientation r t, fAt δ a

def b {r t m n : ℕ} (δ : ℤ) (k : Fin (r + t)) : A r t m n δ :=
  ∑ a : Orientation r t,
    (algebraMap ℂ (A r t m n δ) (βone m n δ (!a.1 k)) + cyclY δ k) * cyclId δ a

def c {r t m n : ℕ} (δ : ℤ) (k : Fin (r + t)) : A r t m n δ :=
  ∑ a : Orientation r t,
    (algebraMap ℂ (A r t m n δ) (βone m n δ (a.1 k)) - cyclY δ k) * cyclId δ a

/-- Inverse of `x u` in the corner `u A u`, with its defining equations. -/
def CornerInverseProperty {r t m n : ℕ} (δ : ℤ)
    (x u g : A r t m n δ) : Prop :=
  g = u * g * u ∧ g * x * u = u ∧ x * u * g = u

def cornerInverse {r t m n : ℕ} (δ : ℤ) (x u : A r t m n δ) : A r t m n δ :=
  by classical exact if h : ∃ g : A r t m n δ, CornerInverseProperty δ x u g then
    Classical.choose h else 0

/-- Section 4 makes a choice of square root in the polynomial algebra of each y.
This predicate states precisely the allowed choices. -/
def IsRootFamily {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ) : Prop :=
  (∀ j a, ∃ p : Polynomial ℂ,
    R j * cyclId δ a =
      p.eval₂ (algebraMap ℂ (A r t m n δ)) (cyclY δ j) * fAt δ a) ∧
  (∀ j, R j * R j = b δ j * f δ)

def q {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) : A r t m n δ :=
  R (next k hk) * cornerInverse δ (R k) (f δ)

def sigma {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t)
    (a : Orientation r t) : A r t m n δ := by
  classical
  exact
  if adjacent a k then
    -(q δ R k hk * cyclTotal δ .s k * q δ R k hk * cyclId δ a) +
      cornerInverse δ (b δ k) (f δ) * fAt δ a
  else 0

def sigmaHat {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t)
    (a : Orientation r t) : A r t m n δ := by
  classical
  exact
  if opposite a k then
    -(q δ R k hk * cyclTotal δ .sh k * q δ R k hk * cyclId δ a)
  else 0

def tau {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t)
    (a : Orientation r t) : A r t m n δ := by
  classical
  exact
  if opposite a k then
    q δ R k hk * cyclTotal δ .e k * q δ R k hk * cyclId δ a
  else 0

def tauHat {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t)
    (a : Orientation r t) : A r t m n δ := by
  classical
  exact
  if opposite a k then
    q δ R k hk * cyclTotal δ .eh k * q δ R k hk * fAt δ a
  else 0

def totalSigma {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) : A r t m n δ :=
  ∑ a : Orientation r t, sigma δ R k hk a

def totalSigmaHat {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) : A r t m n δ :=
  ∑ a : Orientation r t, sigmaHat δ R k hk a

def totalTau {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) : A r t m n δ :=
  ∑ a : Orientation r t, tau δ R k hk a

def totalTauHat {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) : A r t m n δ :=
  ∑ a : Orientation r t, tauHat δ R k hk a

def cornerSubmodule {r t m n : ℕ} (δ : ℤ) (u : A r t m n δ) :
    Submodule ℂ (A r t m n δ) where
  carrier := {x | u * x * u = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change u * (x + y) * u = x + y
    calc
      u * (x + y) * u = u * x * u + u * y * u := by noncomm_ring
      _ = x + y := by rw [hx, hy]
  smul_mem' := by
    intro c x hx
    change u * (c • x) * u = c • x
    calc
      u * (c • x) * u = c • (u * x * u) := by simp [Algebra.smul_def, mul_assoc, Algebra.commutes]
      _ = c • x := by rw [hx]

/-- Assumption 5.5, with the real inequalities read from the integer parameters. -/
def Assumption55 (r t m n : ℕ) (δ : ℤ) : Prop :=
  |((n : ℝ) - (m : ℝ)) / 2| + (r + t : ℝ) <
      -(δ : ℝ) + ((m : ℝ) + (n : ℝ)) / 2 ∧
  |(δ : ℝ) + ((m : ℝ) - (n : ℝ)) / 2| + (r + t : ℝ) <
      ((m : ℝ) + (n : ℝ)) / 2

/-- The images of the Jucys–Murphy recursion (2.7), with the correction of
the printed source idempotent in the mixed case. `j=0` is ξ₁. -/
def xiImage {r t m n : ℕ} (δ : ℤ) (R : Fin (r + t) → A r t m n δ) :
    ℕ → A r t m n δ
  | 0 => 0
  | j + 1 =>
      if h : j + 1 < r + t then
        let k : Fin (r + t) := ⟨j, by omega⟩
        ∑ a : Orientation r t,
          if adjacent a k then
            totalSigma δ R k h * xiImage δ R j * totalSigma δ R k h * cyclId δ a +
              sigma δ R k h a
          else
            totalSigmaHat δ R k h * xiImage δ R j * totalSigmaHat δ R k h *
              cyclId δ a - tau δ R k h a
      else xiImage δ R j

end

end WalledBrauer.LevelTwo


