-- Prove2me | Definitions.Def_GRH_CharacterMoment
-- name    : GRH_CharacterMoment
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T17:20:48.792728+00:00
-- url     : https://prove2.me/theorems/af184b6f-5ea8-4b7b-add9-eed19530fb35
-- title:
--   Arithmetic certificates for centered character sums using multiplicative convolution
-- statement:
--   Fix a witness period $Q$. Start with the indicator of the units between $2$ and the prefix endpoint. Convolve this row with itself on the multiplicative unit group zero or more times. The certificate records the resulting integer rows, an arbitrary integer center for the last row, and a scale $S$. Its sum of absolute deviations bounds the corresponding moment of every nonprincipal character. The rectangle test combines these scaled prefix bounds with integer brackets for rational powers in Abel summation.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletPrefix

namespace GRH.CharacterMoment

/-- Representatives of the units in one period. -/
def units (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun k => k.Coprime q)

def entry (r k : ℕ) : ℕ := if 1 < k ∧ k ≤ r then 1 else 0

def read (a : Array ℕ) (k : ℕ) : ℕ := (a[k]?).getD 0

/-- The two multiplication maps in each row are inverse permutations. -/
def Permutes (q : ℕ) (U : Finset ℕ) (inv : ℕ → ℕ) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, a*b%q ∈ U ∧ inv a*b%q ∈ U ∧
    inv a*(a*b%q)%q=b ∧ a*(inv a*b%q)%q=b

def square (q : ℕ) (U : Finset ℕ) (inv f : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ a ∈ U, f a * f (inv a*k%q)

/-- Each row of natural numbers records one multiplicative convolution square. -/
def Rows (q : ℕ) (U : Finset ℕ) (inv : ℕ → ℕ) (f : ℕ → ℕ) : List (Array ℕ) → Prop
  | [] => True
  | a :: rest => (∀ k ∈ U, read a k = square q U inv f k) ∧ Rows q U inv (read a) rest

instance decRows (q : ℕ) (U : Finset ℕ) (iv f : ℕ → ℕ) (rs : List (Array ℕ)) :
    Decidable (Rows q U iv f rs) :=
  match rs with
  | [] => isTrue trivial
  | a :: rest =>
    letI := decRows q U iv (read a) rest
    inferInstanceAs (Decidable ((∀ k ∈ U, read a k = square q U iv f k) ∧ Rows q U iv (read a) rest))

def lastRow (f : ℕ → ℕ) : List (Array ℕ) → (ℕ → ℕ)
  | [] => f
  | a :: rest => lastRow (read a) rest

def deviation (U : Finset ℕ) (f : ℕ → ℕ) (c : ℕ) : ℕ :=
  ∑ a ∈ U, ((f a-c)+(c-f a))

/-- A finite integer certificate for the centered character sums on one period.
The constant subtracted from the last convolution row can vary with the prefix. -/
def Profile (q S : ℕ) (B : ℕ → ℕ) : Prop :=
  ∃ (U : Finset ℕ) (inv : ℕ → ℕ) (rows : ℕ → List (Array ℕ)) (c : ℕ → ℕ),
    U=units q ∧ Permutes q U inv ∧ S ≤ B 0 ∧
    ∀ r : Fin q, r.val ≠ 0 → Rows q U inv (entry r.val) (rows r.val) ∧
      S^(2^(rows r.val).length) * deviation U (lastRow (entry r.val) (rows r.val)) (c r.val)
        ≤ (B r.val)^(2^(rows r.val).length)

def mass (q M R : ℕ) (B u : ℕ → ℕ) : ℕ :=
  (∑ k ∈ Finset.range M, B ((k+1)%q) * (u (k+1)-(u (k+2)-1))) + R*u (M+1)

/-- A character-independent, finite arithmetic test on a multiple of the modulus. -/
def Covers (d : ℕ) (a b H : ℝ) : Prop :=
  ∃ Q M R D S p t v w : ℕ, ∃ B u : ℕ → ℕ,
    2<Q ∧ d ∣ Q ∧ 0<D ∧ 0<S ∧ 0<p ∧ 0<t ∧ 0<w ∧ (p:ℝ)/t ≤ a ∧
    b^2+H^2 ≤ (((v:ℝ)/w)*((p:ℝ)/t))^2 ∧ Profile Q S B ∧
    (∀ r : Fin Q, B r.val ≤ R) ∧ DirichletPrefix.Table M D p t u ∧
    v*mass Q M R B u < w*D*S

end GRH.CharacterMoment


