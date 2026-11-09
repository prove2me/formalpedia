-- Prove2me | Definitions.Def_HypercliqueAC0_FixedDepth_Planting
-- name    : HypercliqueAC0_FixedDepth_Planting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T19:11:35.937192+00:00
-- url     : https://prove2.me/theorems/ce9b6b03-e0c6-48e7-a0f3-5e952c743554
-- title:
--   Restrictions, spanning, and independent random placement
-- statement:
--   Fix an $r$-uniform hypergraph $G$ on $[m]$ and a hypergraph $H$ with vertices in $[m]$. Only edges of $H$ missing in $G$ remain variables. For a Boolean assignment $z$ to those free edges, put
--
--   $$\rho_H(x_e)=\begin{cases}z_e&e\in E(H)\setminus E(G),\\1&e\in E(G),\\0&\text{otherwise}.\end{cases}$$
--
--   The restricted real function is $g|_{\rho_H}(z)=g(\rho_H(z))$. It spans $H$ precisely when a monomial $E$ of the restricted function touches every vertex of $H$. A separate predicate records a restricted monomial touching more than $s$ vertices.
--
--   For an event $\mathcal E(\iota,G)$ and a uniformly random injection $\iota:[v]\hookrightarrow[m]$ independent of $G\sim\mu_p$, its probability is
--
--   $$\Pr[\mathcal E]=\frac1{\#\{\iota:[v]\hookrightarrow[m]\}}\sum_\iota\sum_G\mu_p(G)1_{\mathcal E(\iota,G)}.$$
--
--   The prefix spanning probability tests every positive prefix against the random image of a fixed labeled hypergraph. The large-gate event tests whether any circuit gate of depth at most $h$ has a monomial touching more than $s$ vertices under the planted restriction. These are the events in Lemmas 4.2, 4.3 and 4.5.
--
--   **Formalization Note** Free variables form exactly the subtype $E(H)\setminus E(G)$. Present edges outside $H$ are fixed to one. The finite average is used only when injections exist, as guaranteed by the theorem bounds on $v$ or $\ell$. The large-gate event is the maximal event described in Lemma 4.5; any event contained in it satisfies the same bound.
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.13 (PDF p.15), §4.1, Lemmas 4.2–4.3 and Lemma 4.5 p.17 (PDF p.19)

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Hypergraphs
import Definitions.Def_HypercliqueAC0_FixedDepth_Fourier
import Definitions.Def_HypercliqueAC0_FixedDepth_Circuits

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Exactly the edges of H missing in G, and no other variables. -/
abbrev FreeEdge {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r) :=
  {e : Edge m r // e ∈ H.edges ∧ G e = false}

/-- ρ_H leaves missing edges of H free; all other edges have their G value. -/
def rho {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (z : FreeEdge G H → Bool) : Edge m r → Bool := fun e =>
  if he : e ∈ H.edges ∧ G e = false then z ⟨e, he⟩ else G e

def restricted {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (g : (Edge m r → Bool) → ℝ) : (FreeEdge G H → Bool) → ℝ := fun z => g (rho G H z)

/-- Every vertex of H must be touched, including isolated vertices. -/
def spans {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (g : (Edge m r → Bool) → ℝ) : Prop :=
  ∃ E : Finset (FreeEdge G H), isMonomial (restricted G H g) E ∧
    H.vertices ⊆ verticesOf (E.image (fun e => e.val))

def hasLargeMonomial {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (g : (Edge m r → Bool) → ℝ) (s : ℕ) : Prop :=
  ∃ E : Finset (FreeEdge G H), isMonomial (restricted G H g) E ∧
    s < (verticesOf (E.image (fun e => e.val))).card

/-- Uniform injection, independently of the Bernoulli hypergraph. -/
def jointProbability {v m r : ℕ} (p : ℝ)
    (event : (Fin v ↪ Fin m) → (Edge m r → Bool) → Prop) : ℝ :=
  (Fintype.card (Fin v ↪ Fin m) : ℝ)⁻¹ *
    ∑ ι : Fin v ↪ Fin m, probability p (event ι)

/-- Probability that a positive prefix spans a random image of H₀. -/
def prefixSpanningProbability {v m r : ℕ} (p : ℝ) (H₀ : Finset (Edge v r))
    (isAnd : Bool) (inputs : List ((Edge m r → Bool) → Bool)) : ℝ :=
  jointProbability p (fun ι G => ∃ j : ℕ, 1 ≤ j ∧ j ≤ inputs.length ∧
    spans G (imageHypergraph H₀ ι) (boolReal (abstractPrefix isAnd inputs j)))

/-- The maximal event described in Lemma 4.5. -/
def largeGateProbability {m r : ℕ} (p : ℝ) (ℓ h s : ℕ)
    (C : MantriCVQ.ACCircuit (Edge m r)) : ℝ :=
  jointProbability p (fun (ι : Fin ℓ ↪ Fin m) G =>
    ∃ k : Fin C.gates.length, gateDepth C k ≤ h ∧
      hasLargeMonomial G (complete r (Finset.univ.map ι)) (boolReal (gateValue C k)) s)

end HypercliqueAC0.FixedDepth


