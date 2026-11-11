-- Prove2me | Definitions.Def_JainCRERepetition_Cubic_registers
-- name    : JainCRERepetition_Cubic_registers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:27.210033+00:00
-- url     : https://prove2.me/theorems/f0f15385-c9b3-4ad1-b8ed-6bf56809c36f
-- title:
--   Definitions 2.3, 2.4 and 2.6 — named registers and conditional comparisons
-- statement:
--   A subsystem is a finite set of named registers, each carrying its own finite basis. Matrices on the product basis support explicit partial traces, conditioning projectors, record probabilities and separately normalized conditional marginals. Classical records are diagonal only on the designated registers; matching copies retain coherent off-diagonal blocks between different matching labels.
--
--   For a prior $\mu$, the conditional comparison map attaches the remote copied question by
--
--   $$\mathcal C_A^\mu(\tau)=\sum_y |y\rangle\langle y|\otimes K_y^\mu\tau K_y^\mu,\qquad K_y^\mu=\sum_x\sqrt{\mu(y\mid x)}|x\rangle\langle x|.$$
--
--   The seed is a density operator supported on matching local copies and on the positive marginal support of $\mu$. Named-register comparisons require that all three distinct question registers actually occur. Conditioning on zero mass is assigned zero and is never used as a normalized supported block. This interface permits exact coordinate restrictions without changing comparison weights or optimizing a comparison separately at each prefix.
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), pp. 10–12, Definitions 2.3, 2.4, 2.6; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_quantum

open scoped BigOperators
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic

/-- A subsystem consists of named registers, each with its own finite distinguished basis. -/
abbrev Config {R : Type} (V : R → Type) (s : Finset R) := (r : {r // r ∈ s}) → V r.val

section Registers
variable {R : Type} [Fintype R] [DecidableEq R]
variable (V : R → Type) [∀ r, Fintype (V r)] [∀ r, DecidableEq (V r)]
variable [∀ r, Nonempty (V r)]

def readReg {s : Finset R} (a : Config V s) (r : R) : V r :=
  if h : r ∈ s then a ⟨r,h⟩ else Classical.choice (inferInstance : Nonempty (V r))

def restrictReg {s : Finset R} (a : Config V s) (t : Finset R) : Config V t :=
  fun r => readReg V a r.val

/-- Partial trace, with the distinguished bases ordered by the register names. -/
def reduced {s : Finset R} (ρ : Op (Config V s)) (t : Finset R) : Op (Config V t) :=
  fun a b => ∑ u : Config V s, ∑ v : Config V s,
    if restrictReg V u t = a ∧ restrictReg V v t = b ∧
        (∀ r ∈ s \ t, readReg V u r = readReg V v r) then ρ u v else 0

def selected {s : Finset R} (ρ : Op (Config V s)) (t : Finset R) (h : Config V t) :
    Op (Config V s) :=
  fun a b => if restrictReg V a t = h ∧ restrictReg V b t = h then ρ a b else 0

def recordProb {s : Finset R} (ρ : Op (Config V s)) (t : Finset R) (h : Config V t) : ℝ :=
  (selected V ρ t h).trace.re

def conditioned {s : Finset R} (ρ : Op (Config V s)) (t : Finset R)
    (h : Config V t) (keep : Finset R) : Op (Config V keep) :=
  (recordProb V ρ t h : ℂ)⁻¹ • reduced V (selected V ρ t h) keep

def classicalOn {s : Finset R} (ρ : Op (Config V s)) (t : Finset R) : Prop :=
  ∀ a b, restrictReg V a t ≠ restrictReg V b t → ρ a b = 0

def matchingOn {s : Finset R} (ρ : Op (Config V s)) (xh x : R) (e : V xh ≃ V x) : Prop :=
  ∀ a b, (e (readReg V a xh) ≠ readReg V a x ∨
    e (readReg V b xh) ≠ readReg V b x) → ρ a b = 0

/-- Attach the remote conditional law, retaining coherent local copied-input blocks. -/
def attach {s : Finset R} (x yh : R) (μ : Law (V x × V yh))
    (τ : Op (Config V (s.erase yh))) : Op (Config V s) :=
  fun a b => if readReg V a yh = readReg V b yh then
    (Real.sqrt (kernel μ.p (readReg V a x) (readReg V a yh)) : ℂ) *
    (Real.sqrt (kernel μ.p (readReg V b x) (readReg V b yh)) : ℂ) *
    τ (restrictReg V a (s.erase yh)) (restrictReg V b (s.erase yh)) else 0

def RegComparison {s : Finset R} (xh x yh : R) (e : V xh ≃ V x)
    (μ : Law (V x × V yh)) (ν : Op (Config V s)) : Prop :=
  xh ∈ s ∧ x ∈ s ∧ yh ∈ s ∧ xh ≠ x ∧ xh ≠ yh ∧ x ≠ yh ∧
  ∃ τ : Op (Config V (s.erase yh)), IsState τ ∧ matchingOn V τ xh x e ∧
    (∀ a, marginalX μ.p (readReg V a x) = 0 → τ a a = 0) ∧ ν = attach V x yh μ τ

end Registers
end JainCRERepetition.Cubic


