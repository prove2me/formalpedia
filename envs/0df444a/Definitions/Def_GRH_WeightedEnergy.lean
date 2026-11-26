-- Prove2me | Definitions.Def_GRH_WeightedEnergy
-- name    : GRH_WeightedEnergy
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T18:06:57.587423+00:00
-- url     : https://prove2.me/theorems/4556f055-7ef6-54d5-b5c5-a23e2ad2e84c
-- title:
--   Weighted autocorrelation certificates for Abel bounds
-- statement:
--   A certificate groups the rounded Abel variation by character prefix, forms a weighted autocorrelation on the finite group of units, and checks an integer moment bound. A passing certificate covers a rectangle at every divisor of the witness modulus.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_CharacterMoment

namespace GRH.WeightedEnergy
open CharacterMoment

/-- Integer witnesses for Abel variation and the common-character second moment. -/
structure Data where
  Q : ℕ
  M : ℕ
  R : ℕ
  D : ℕ
  p : ℕ
  t : ℕ
  v : ℕ
  w : ℕ
  L : ℕ
  c : ℕ
  U : Finset ℕ
  I : Finset ℕ
  inv : ℕ → ℕ
  key : ℕ → ℕ
  W : ℕ → ℕ
  scale : ℕ → ℕ
  dual : ℕ → ℕ
  u : ℕ → ℕ
  T : ℕ → ℕ
  rows : List (Array ℕ)

def keys (g : Data) := insert 0 (insert 1 g.I)

def delta (u : ℕ → ℕ) (k : ℕ) := u (k+1)-(u (k+2)-1)

def weightSum (Q M : ℕ) (u key : ℕ → ℕ) (i : ℕ) :=
  ∑ k ∈ Finset.range M, if key ((k+1)%Q)=i then delta u k else 0

def correlation (g : Data) (k : ℕ) := ∑ i ∈ g.I, g.W i*g.dual i *
  (∑ b ∈ g.U, entry i b * entry i (b*k%g.Q))

def budget (g : Data) := g.w*g.D-g.v*(g.W 0+g.R*g.u (g.M+1))

def Valid (g : Data) : Prop :=
  2<g.Q ∧ 0<g.D ∧ 0<g.p ∧ 0<g.t ∧ 0<g.w ∧ 0<g.L ∧ 0<g.R ∧
  g.Q.totient ≤ 2*g.R ∧ g.U=units g.Q ∧ Permutes g.Q g.U g.inv ∧
  0∉g.I ∧ 1∉g.I ∧ g.key 0=0 ∧
  (∀ r : Fin g.Q, r.val≠0 → (g.key r.val=1 ∨ g.key r.val∈g.I) ∧
    ∀ b ∈ g.U, entry r.val b=entry (g.key r.val) b) ∧
  (∀ i ∈ keys g, g.W i=weightSum g.Q g.M g.u g.key i) ∧
  (∀ i ∈ g.I, g.scale i*g.dual i=g.L) ∧ (∀ k ∈ g.U, g.T k=correlation g k) ∧
  Rows g.Q g.U g.inv g.T g.rows ∧ DirichletPrefix.Table g.M g.D g.p g.t g.u ∧
  0<budget g ∧ g.v^(2*2^g.rows.length)*(∑ i ∈ g.I, g.W i*g.scale i)^(2^g.rows.length)*
    deviation g.U (lastRow g.T g.rows) g.c < (budget g)^(2*2^g.rows.length)*g.L^(2^g.rows.length)

/-- A sufficient finite test for every character on a divisor of the witness period. -/
def Covers (d : ℕ) (a b H : ℝ) : Prop := ∃ g : Data, Valid g ∧ d ∣ g.Q ∧
  (g.p:ℝ)/g.t ≤ a ∧ b^2+H^2 ≤ (((g.v:ℝ)/g.w)*((g.p:ℝ)/g.t))^2

end GRH.WeightedEnergy


