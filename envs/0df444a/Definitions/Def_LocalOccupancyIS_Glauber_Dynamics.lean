-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
-- name    : LocalOccupancyIS_Glauber_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:57:31.812538+00:00
-- url     : https://prove2.me/theorems/2ebcd8d1-bf31-4642-9f4d-482dacf0930e
-- title:
--   Conditional heat-bath, fixed words, entropy and certificates
-- statement:
--   For a finite graph $G$ and $\lambda>0$, resampling a block $A$ assigns to each feasible configuration agreeing with the input off $A$ its normalized hard-core weight. Let $P_u$ use $A=\{u\}$ and $Q_u$ use the open neighborhood $A=N(u)$, so the center remains fixed under $Q_u$. Ordinary dynamics uses the published random-scan matrix $K$. Laws act on the left. With natural logarithms and the convention $0\log0=0$, the finite relative entropy and total variation distance are
--
--   $$D(\nu\|\mu)=\sum_x\nu(x)\log\frac{\nu(x)}{\mu(x)},\qquad d_{TV}(\nu,\mu)=\frac12\sum_x|\nu(x)-\mu(x)|.$$
--
--   Entropy is used only where domination is established; its formula is not interpreted as extended KL on singular laws. Fixed deterministic lists of neighbors define products of single-site kernels. Their occurrence bound is the maximum, over vertices, of the sum of occurrences across every full word. A sweep visits its specified finite set once. A prefix list is nonempty and contains only lengths within its full word. The score and certificates are
--
--   $$g_u(I)=\beta p\mathbf1_{I\cap N(u)=\varnothing}+\gamma|I\cap N(u)|,\qquad \mathbb E_{\nu S_u}g_u\ge1-\eta,$$
--
--   or the arithmetic average of these expectations over fixed prefixes. Finally $H_\lambda=n\log((1+\lambda)/\min\{1,\lambda\})$ and the time-averaged cardinality is $T^{-1}\sum_{j<T}\mathbb E_{\nu K^j}|I|$. These definitions impose neither certificate success nor full support on an input law.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), §§1.1–2, equations (2), (4), (6), p. 3–8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=3

import Definitions.Def_LocalOccupancyIS_Glauber_GraphModel

open scoped BigOperators

namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Conditional heat-bath on a block A; the exterior remains fixed. -/
def heatBath (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (A : Finset V) :
    Matrix (State G) (State G) ℝ := fun σ τ =>
  if ∀ v ∉ A, τ.val v = σ.val v then
    HardCoreBochner.hcLaw G lam τ /
      ∑ ζ : State G, if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0
  else 0

def P (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (u : V) :=
  heatBath G lam {u}

def Q (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (u : V) :=
  heatBath G lam (G.neighborFinset u)

/-- Published random-scan chain, on a nonempty vertex set. -/
def K (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) := HardCoreBochner.hcChain G lam

def push {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (A : Matrix Ω Ω ℝ) : Ω → ℝ :=
  Matrix.vecMul ν A

def point {Ω : Type} [DecidableEq Ω] (x : Ω) : Ω → ℝ := fun y => if y = x then 1 else 0

/-- KL in nats. Used with absolute continuity, established as conclusions below. -/
def kl {Ω : Type} [Fintype Ω] (ν μ : Ω → ℝ) : ℝ :=
  ∑ x, if ν x = 0 then 0 else ν x * Real.log (ν x / μ x)

def Dominated {Ω : Type} (ν μ : Ω → ℝ) : Prop := ∀ x, ν x ≠ 0 → 0 < μ x

def tv {Ω : Type} [Fintype Ω] (ν μ : Ω → ℝ) : ℝ := (∑ x, |ν x - μ x|) / 2

def entropyBound (n : ℕ) (lam : ℝ) : ℝ := n * Real.log ((1 + lam) / min 1 lam)

def word (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (w : List V) :
    Matrix (State G) (State G) ℝ := (w.map (P G lam)).prod

def NeighborhoodWords (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → List V) : Prop :=
  ∀ u, ∀ v ∈ w u, G.Adj u v

def IsSweep (A : Finset V) (w : List V) : Prop := w.Nodup ∧ w.toFinset = A

/-- Occurrences summed over all full words, then maximized over vertices. -/
def occurrences (w : V → List V) : ℕ :=
  Finset.univ.sup (fun v => ∑ u, (w u).count v)

def score (G : SimpleGraph V) [DecidableRel G.Adj] (lam β γ : ℝ) (u : V) (σ : State G) : ℝ :=
  β * p lam * (if nbrSize G u σ.val = 0 then 1 else 0) + γ * nbrSize G u σ.val

def WordCertificate (G : SimpleGraph V) [DecidableRel G.Adj] (lam β γ η : ℝ)
    (w : V → List V) : Prop :=
  ∀ ν : State G → ℝ, MarkovMixing.IsDist ν → ∀ u,
    1 - η ≤ expectation (push ν (word G lam (w u))) (score G lam β γ u)

/-- A nonempty list of deterministic prefix lengths, each within its full word. -/
def Prefixes (w : V → List V) (a : V → List ℕ) : Prop :=
  ∀ u, (a u).length > 0 ∧ ∀ j ∈ a u, j ≤ (w u).length

def PrefixCertificate (G : SimpleGraph V) [DecidableRel G.Adj] (lam β γ η : ℝ)
    (w : V → List V) (a : V → List ℕ) : Prop :=
  ∀ ν : State G → ℝ, MarkovMixing.IsDist ν → ∀ u,
    1 - η ≤ ((a u).map (fun j =>
      expectation (push ν (word G lam ((w u).take j))) (score G lam β γ u))).sum /
        (a u).length

/-- E|I_J|, J uniform and independent in {0,...,T-1}. T is required positive. -/
def timeMean (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (ν : State G → ℝ) (T : ℕ) : ℝ :=
  (∑ j ∈ Finset.range T, expectation (push ν (K G lam ^ j)) (fun σ => size σ.val)) / T

end
end LocalOccupancyIS.Glauber


