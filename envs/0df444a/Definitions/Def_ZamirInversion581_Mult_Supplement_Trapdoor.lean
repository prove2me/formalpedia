-- Prove2me | Definitions.Def_ZamirInversion581_Mult_Supplement_Trapdoor
-- name    : ZamirInversion581_Mult_Supplement_Trapdoor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:49:15.145879+00:00
-- url     : https://prove2.me/theorems/f8686ed2-708f-4379-843a-81f00c31a299
-- title:
--   Trapdoored matrices with exact fast forward action
-- statement:
--   Fix a finite field $F$. A trapdoor object consists of a sampler program $\mathrm{Samp}$ and a forward-action program $\mathrm{Act}$ in the same field RAM. It satisfies the trapdoor assumption when there are $C>0$ and $b\in\mathbb N$ such that, on dimension $n$, every sampler run outputs a dense $n\times n$ matrix $R$ and a finite trapdoor block $\tau$ within $C(n+2)^2\log(n+2)^b$ operations. On every supported pair and every vector $v\in F^n$, every action run outputs exactly $Rv$ within $C(n+2)\log(n+2)^b$ operations. The action input is $n$, the trapdoor, and the vector; it is not given the dense matrix.
--
--   For every nonuniform probabilistic polynomial-time bit distinguisher family $D_n$, there is a negligible function $\nu$ such that
--   $$
--   \left|\Pr[D_n(R)=1]-\Pr[D_n(U)=1]\right|\le\nu(n)\quad\text{for every }n,
--   $$
--   where $U$ is uniform on all $n\times n$ matrices and the distinguisher sees only $R$. Negligibility uses the published condition $n^k\nu(n)\to0$ for every natural $k$.
--
--   This records precisely the assumed capabilities from §3.1. Determinant computation, transpose action, inversion, and multi-sample security are consequences to be proved, not fields of the assumption. Dense matrices and vectors use row-major and coordinate-order block encodings. The shifts by two in the runtime bounds handle small dimensions without changing the asymptotic requirement.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.11, §3.1 trapdoored-matrix assumption. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Supplement_FieldRAM
import Definitions.Def_ZamirInversion581_Mult_Supplement_Statistics
import Definitions.Def_MLManagesComplexity_Negligible

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-! §3.1, p.11: only fast sampling, exact forward action, and single-sample
nonuniform computational indistinguishability are assumed. No determinant,
transpose, inverse, or multi-sample guarantee is a field of this interface. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Row-major dense encoding. -/
def matrixBlock {n : ℕ} (X : Mat F n) : List F :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => X i j))

def vectorBlock {n : ℕ} (v : Fin n → F) : List F := (List.finRange n).map v

/-- Decode the already exposed dense block. -/
def blockMatrix (n : ℕ) (xs : List F) : Mat F n :=
  fun i j => xs.getD (n * i.val + j.val) 0

/-- Total decoding; the sampler's validity clause excludes the default case. -/
def sampleData (n : ℕ) (σ : Config F) : Mat F n × List F :=
  match σ.status with
  | .done (some (.blocks xs τ)) => (blockMatrix n xs, τ)
  | _ => (0, [])

/-- Source objects are programs, not arbitrary fast maps. -/
structure TrapdoorPrograms (F : Type*) where
  sampler : Program F
  action : Program F

noncomputable def samplerLaw (𝒯 : TrapdoorPrograms F) (n : ℕ) : PMF (Config F) :=
  finalLaw 𝒯.sampler (blockInput [n] [])

/-- Input n, trapdoor length; memory is the trapdoor followed by the vector. -/
def actionInput (n : ℕ) (τ : List F) (v : Fin n → F) : Config F :=
  blockInput [n, τ.length] (τ ++ vectorBlock v)

/-- Trapdoored-matrix assumption, with constants belonging to the fixed family.
Every random branch of the sampler returns n² field cells and a finite trapdoor.
Every supported pair has an exact forward action for every vector. -/
def IsTrapdoored (𝒯 : TrapdoorPrograms F) : Prop :=
  (∃ (C : ℝ) (b : ℕ), 0 < C ∧ ∀ n,
    HaltWithin 𝒯.sampler (blockInput [n] [])
      (C * (n + 2 : ℝ) ^ 2 * Real.log (n + 2 : ℝ) ^ b) ∧
    ∀ σ ∈ (samplerLaw 𝒯 n).support,
      (∃ xs τ, σ.status = .done (some (.blocks xs τ)) ∧ xs.length = n * n) ∧
      ∀ v : Fin n → F,
        let Rτ := sampleData n σ
        HaltWithin 𝒯.action (actionInput n Rτ.2 v)
          (C * (n + 2 : ℝ) * Real.log (n + 2 : ℝ) ^ b) ∧
        ∀ δ ∈ (finalLaw 𝒯.action (actionInput n Rτ.2 v)).support,
          δ.status = .done (some (.block (vectorBlock (Rτ.1.mulVec v))))) ∧
  ∀ D : ℕ → Program F, NonuniformPPT D →
    ∃ ν : ℕ → ℝ, MLManagesComplexity.Negligible ν ∧ ∀ n,
      |(eventProb ((samplerLaw 𝒯 n).bind (fun σ =>
          finalLaw (D n) (matrixInput n [n] (sampleData n σ).1)))
          (fun δ => δ.status = .done (some (.index 1)))) -
        (unifMean (fun X : Mat F n => accepts (D n) (matrixInput n [n] X)
          (fun o => o = .index 1)))| ≤ ν n

end ZamirInversion581.Mult.Supplement


