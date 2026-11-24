-- Prove2me | Definitions.Def_proofs_PhosphorylationSharpness_Source
-- name    : proofs_PhosphorylationSharpness_Source
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:19:11.919274+00:00
-- url     : https://prove2.me/theorems/200a24c6-ed68-438c-9997-542dcb6fd65e
-- title:
--   Source
-- statement:
--   Definitions and structural lemmas for Source, from mmislan (mmislan/palomar-p080-phosphorylation-attainment; see pinned Apache-2.0 LICENSE)'s pinned Sharp lower bound on positive equilibria in sequential distributive phosphorylation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Source.lean

import Mathlib
set_option autoImplicit true
namespace PhosphorylationSharpness
noncomputable section
open scoped BigOperators
structure State (n : ℕ) where
  S : Fin (n+1) → ℝ
  E : ℝ
  F : ℝ
  C : Fin n → ℝ
  D : Fin n → ℝ
structure Rates (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  c : Fin n → ℝ
  alpha : Fin n → ℝ
  beta : Fin n → ℝ
  gamma : Fin n → ℝ
def Rates.Positive {n : ℕ} (k : Rates n) : Prop :=
  ∀ i, 0 < k.a i ∧ 0 < k.b i ∧ 0 < k.c i ∧
    0 < k.alpha i ∧ 0 < k.beta i ∧ 0 < k.gamma i
def State.Positive {n : ℕ} (x : State n) : Prop :=
  (∀ i, 0 < x.S i) ∧ 0 < x.E ∧ 0 < x.F ∧ (∀ i, 0 < x.C i) ∧ (∀ i, 0 < x.D i)
def kinaseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ :=
  k.a i*x.S i.castSucc*x.E-k.b i*x.C i
def phosphataseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ :=
  k.alpha i*x.S i.succ*x.F-k.beta i*x.D i
def field {n : ℕ} (k : Rates n) (x : State n) : State n where
  S j := ∑ i : Fin n, (
    (if i.castSucc = j then -kinaseNet k x i+k.gamma i*x.D i else 0) +
    (if i.succ = j then k.c i*x.C i-phosphataseNet k x i else 0))
  E := ∑ i, (-kinaseNet k x i+k.c i*x.C i)
  F := ∑ i, (-phosphataseNet k x i+k.gamma i*x.D i)
  C i := kinaseNet k x i-k.c i*x.C i
  D i := phosphataseNet k x i-k.gamma i*x.D i
def Equilibrium {n : ℕ} (k : Rates n) (x : State n) : Prop :=
  (∀ i, (field k x).S i=0) ∧ (field k x).E=0 ∧ (field k x).F=0 ∧
    (∀ i, (field k x).C i=0) ∧ (∀ i, (field k x).D i=0)
def totalE {n : ℕ} (x : State n) : ℝ := x.E+∑ i, x.C i
def totalF {n : ℕ} (x : State n) : ℝ := x.F+∑ i, x.D i
def totalS {n : ℕ} (x : State n) : ℝ := (∑ i, x.S i)+(∑ i, x.C i)+(∑ i, x.D i)
def realize {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ) : Rates n where
  a i := 2*D i/t i.castSucc
  b i := D i/B i
  c i := D i/B i
  alpha i := 2*D i/t i.succ
  beta _ := 1
  gamma _ := 1
def reconstruct {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) : State n where
  S i := t i*u^i.val*s
  E := u*f
  F := f
  C i := B i*u^(i.val+1)*s*f
  D i := D i*u^(i.val+1)*s*f
def inventory {n : ℕ} (t : Fin n → ℝ) (u : ℝ) : ℝ := ∑ i, t i*u^i.val
end
end PhosphorylationSharpness


