-- Prove2me | Definitions.Def_QReversal_PGMBound_Setting
-- name    : QReversal_PGMBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:45.76262+00:00
-- url     : https://prove2.me/theorems/4889f663-e700-42f2-a03c-6deda2406f39
-- title:
--   Equations (10), (12), (35)–(36): spectral ensembles, channel, reversal and fidelities
-- statement:
--   Let $J$ label the input basis and $O$ the eigenvectors of each output state. Probabilities $p_j\geq0$ sum to one. For each $j$, the nonnegative eigenvalues $\lambda_{ij}$ sum to one and the vectors $v_{ij}$, indexed by $i\in O$, are orthonormal. Set $\hat\rho_j=\sum_i\lambda_{ij}|v_{ij}\rangle\langle v_{ij}|$ and $\rho=\sum_jp_j|j\rangle\langle j|$.
--
--   The classicizing channel has operators $A_{ij}=\sqrt{\lambda_{ij}}|v_{ij}\rangle\langle j|$. For any Kraus family $A$, its reversal family is
--   $$
--   (R_{A,\rho})_i=\rho^{1/2}A_i^\dagger A(\rho)^{-1/2}.
--   $$
--   The module also defines classical fidelity by (10), Bures–Uhlmann fidelity by $F_{\mathrm{BU}}(\sigma,\tau)=\operatorname{tr}\sqrt{\sqrt\sigma\,\tau\,\sqrt\sigma}$, the output and weighted states, and the arrays $A,R$ of page 12.
--
--   These objects support the bound and its intermediate identities.
--
--   **Formalization Note** The Kraus action is the published PeresTerno.krausUpdate. The inverse square root inverts nonzero eigenvalues and leaves zero eigenvalues at zero, as on page 7.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, pp. 5, 7, 10–12, (10), (12), (35)–(36)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder

namespace QReversal.PGMBound

def IsProbability {J : Type*} [Fintype J] (p : J → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1

def IsSpectralData {J O : Type*} [Fintype O] [DecidableEq O]
    (lam : O → J → ℝ) (v : O → J → O → ℂ) : Prop :=
  (∀ i j, 0 ≤ lam i j) ∧
  (∀ j, ∑ i, lam i j = 1) ∧
  (∀ j i i', star (v i j) ⬝ᵥ v i' j = if i = i' then 1 else 0)

noncomputable def rhoHat {J O : Type*} [Fintype O] [DecidableEq O]
    (lam : O → J → ℝ) (v : O → J → O → ℂ) (j : J) : Matrix O O ℂ :=
  ∑ i, (lam i j : ℂ) • vecMulVec (v i j) (star (v i j))

noncomputable def classicKraus {J O : Type*} [DecidableEq J]
    (lam : O → J → ℝ) (v : O → J → O → ℂ) : O × J → Matrix O J ℂ :=
  fun ij => (Real.sqrt (lam ij.1 ij.2) : ℂ) •
    vecMulVec (v ij.1 ij.2) (Pi.single ij.2 1)

noncomputable def rho {J : Type*} [DecidableEq J] (p : J → ℝ) : Matrix J J ℂ :=
  Matrix.diagonal (fun j => (p j : ℂ))

noncomputable def reversal {J O ι : Type*} [Fintype J] [DecidableEq J] [Fintype O]
    [DecidableEq O] [Fintype ι]
    (A : ι → Matrix O J ℂ) (X : Matrix J J ℂ) : ι → Matrix J O ℂ :=
  fun i => CFC.sqrt X * (A i)ᴴ * QReversal.NearOpt.invSqrt (krausUpdate A X)

noncomputable def comp {J O ι κ : Type*} [Fintype O]
    (R : κ → Matrix J O ℂ) (A : ι → Matrix O J ℂ) : κ × ι → Matrix J J ℂ :=
  fun ki => R ki.1 * A ki.2

noncomputable def rhoOut {J O : Type*} [Fintype J] [Fintype O]
    [DecidableEq J] (p : J → ℝ) (lam : O → J → ℝ)
    (v : O → J → O → ℂ) : Matrix O O ℂ :=
  krausUpdate (classicKraus lam v) (rho p)

noncomputable def weightedState {J O : Type*} [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (j : J) : Matrix O O ℂ :=
  (p j : ℂ) • rhoHat lam v j

noncomputable def Fcl {J κ : Type*} [Fintype J] [DecidableEq J]
    [Fintype κ] (p : J → ℝ) (K : κ → Matrix J J ℂ) : ℝ :=
  ∑ j, p j * (krausUpdate K (Matrix.single j j 1) j j).re

noncomputable def FBU {O : Type*} [Fintype O] [DecidableEq O]
    (σ₁ σ₂ : Matrix O O ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt σ₁ * σ₂ * CFC.sqrt σ₁))).re

noncomputable def Amat {J O : Type*} [Fintype J] [Fintype O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) :
    Matrix O (J × O) ℂ :=
  fun o ji => (Real.sqrt (p ji.1) * Real.sqrt (lam ji.2 ji.1) : ℂ) * v ji.2 ji.1 o

noncomputable def Rmat {J O : Type*} [Fintype J] [Fintype O]
    [DecidableEq O] (p : J → ℝ) (lam : O → J → ℝ)
    (v : O → J → O → ℂ) : Matrix (J × O) O ℂ :=
  (Amat p lam v)ᴴ * QReversal.NearOpt.invSqrt (Amat p lam v * (Amat p lam v)ᴴ)

noncomputable def Bblk {J O : Type*} [Fintype J] [Fintype O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (k l : J) : Matrix O O ℂ :=
  fun i i' => ((Amat p lam v)ᴴ * Amat p lam v) (k, i) (l, i')

end QReversal.PGMBound


