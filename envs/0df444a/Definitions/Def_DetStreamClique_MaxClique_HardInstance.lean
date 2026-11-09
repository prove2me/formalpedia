-- Prove2me | Definitions.Def_DetStreamClique_MaxClique_HardInstance
-- name    : DetStreamClique_MaxClique_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:07:54.443395+00:00
-- url     : https://prove2.me/theorems/8ed600bb-8e96-4ae6-a21b-f44192b9d316
-- title:
--   Input Distribution 3.2.2 and its information quantities
-- statement:
--   Write $k=9b\in\mathbb N$ for the gadget parameter, independently of the approximation ratio $\beta$. A block system consists of $\ell$ subsets $B_i\subseteq\operatorname{Fin}(n)$ with $|B_i|=2k$ and pairwise intersections of size at most one. Independently of a uniform $G_0\sim G_{n,1/2}$, sample a tuple $A$ uniformly from the Cartesian product of the $k$-subsets of the blocks. Thus its coordinates are independent and uniform.
--
--   Given a deterministic protocol $\pi$, construct
--   $$E_A(G_0,A)=\bigcup_i E(G_0[A_i]),\qquad m=\pi(E_A).$$
--   The fiber consists of all legal tuples with this message at fixed $G_0$. Its projection to coordinate $i$ is $m^{-1}|_i$, and $C_i$ is the intersection of that projected family. Bob's graph, for a chosen $A'_i$, is
--   $$E_B=E(\overline G_0[A'_i\setminus C_i]).$$
--   Joint and coordinate information are the corresponding entropy drops at fixed $G_0$; a minimizing index is chosen from the coordinate information values. The graph probability uses the published $G(n,p)$ finite-sum law at $p=1/2$. The joint expectation and probability average over this graph law and the independent uniform tuple law.
--
--   Every block has a $k$-subset, derived from its cardinality. Empty fibers produce $C_i=V$ under the total intersection convention; theorems use only messages in the range. A minimizing index is defined when $\ell>0$; all ties are permitted. No graph properties, information inequalities or hardness claims are assumed by the definitions.
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Input Distribution 3.2.2, p. 16; Definition 2.1, p. 9

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Graphs
import Definitions.Def_DetStreamClique_MaxClique_Information
import Definitions.Def_BollobasChromatic_Main_Setting

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- k=9b: block size 2k=18b, with each edge in at most one block. -/
structure BlockSystem (n ℓ k : ℕ) where
  block : Fin ℓ → Finset (Fin n)
  card_block : ∀ i, (block i).card = 2 * k
  overlap : ∀ i j, i ≠ j → ((block i) ∩ (block j)).card ≤ 1

abbrev Choice {n : ℕ} (B : Finset (Fin n)) (k : ℕ) :=
  {s : Finset (Fin n) // s ⊆ B ∧ s.card = k}

instance choiceNonempty {n ℓ k : ℕ} (B : BlockSystem n ℓ k) (i : Fin ℓ) :
    Nonempty (Choice (B.block i) k) := by
  obtain ⟨s, hs, hc⟩ := Finset.exists_subset_card_eq
    (show k ≤ (B.block i).card by rw [B.card_block]; omega)
  exact ⟨⟨s, hs, hc⟩⟩

abbrev Tuple {n ℓ k : ℕ} (B : BlockSystem n ℓ k) :=
  (i : Fin ℓ) → Choice (B.block i) k

/-- Uniform on the Cartesian product: independent uniform k-subsets. -/
noncomputable def tupleLaw {n ℓ k : ℕ} (B : BlockSystem n ℓ k) : FiniteLaw (Tuple B) :=
  OAI.ThorpCompatibility.Law.uniform

noncomputable def aliceGraph {n ℓ k : ℕ} {B : BlockSystem n ℓ k}
    (G : Graph n) (A : Tuple B) : Graph n :=
  ⨆ i, inducedEdges G (A i).val

noncomputable def fiber {n ℓ k : ℕ} {M : Type} [Fintype M]
    (B : BlockSystem n ℓ k)
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n))) (G : Graph n) (m : M) :
    Finset (Tuple B) :=
  Finset.univ.filter (fun A => π.send (aliceGraph G A) = m)

noncomputable def projectedFiber {n ℓ k : ℕ} {M : Type} [Fintype M]
    (B : BlockSystem n ℓ k)
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) (i : Fin ℓ) : Finset (Finset (Fin n)) :=
  (fiber B π G m).image (fun A => (A i).val)

/-- Intersection of the projected fiber. Empty fibers return all vertices;
all information and output statements require m in the range. -/
noncomputable def commonCore {n ℓ k : ℕ} {M : Type} [Fintype M]
    (B : BlockSystem n ℓ k)
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) (i : Fin ℓ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∀ a ∈ projectedFiber B π G m i, v ∈ a)

noncomputable def bobGraph {n ℓ k : ℕ} {M : Type} [Fintype M]
    (B : BlockSystem n ℓ k)
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) (i : Fin ℓ) (a' : Finset (Fin n)) : Graph n :=
  inducedEdges Gᶜ (a' \ commonCore B π G m i)

/-- Joint information at a fixed base graph: conditioning on G leaves tupleLaw unchanged. -/
noncomputable def jointInfo {n ℓ k : ℕ} {M : Type} [Fintype M]
    (B : BlockSystem n ℓ k)
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) : ℝ :=
  entropyBits (tupleLaw B) id -
    eventEntropy (tupleLaw B) id (fun A => π.send (aliceGraph G A) = m)

noncomputable def coordinateInfo {n ℓ k : ℕ} {M : Type} [Fintype M]
    (B : BlockSystem n ℓ k)
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) (i : Fin ℓ) : ℝ :=
  entropyBits (tupleLaw B) (fun A => (A i).val) -
    eventEntropy (tupleLaw B) (fun A => (A i).val)
      (fun A => π.send (aliceGraph G A) = m)

/-- A specified minimizing index; ties may be broken arbitrarily. -/
noncomputable def minIndex {n ℓ k : ℕ} [NeZero ℓ] {M : Type} [Fintype M]
    (B : BlockSystem n ℓ k)
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) : Fin ℓ :=
  Classical.choose (Finset.exists_min_image Finset.univ (coordinateInfo B π G m)
    Finset.univ_nonempty)

/-- Uniform G(n,1/2), reusing the published G(n,p) definition. -/
noncomputable def graphProbability (n : ℕ) (P : Graph n → Prop) : ℝ :=
  BollobasChromatic.Main.gnpProb n (1/2) P

noncomputable def hardProbability {n ℓ k : ℕ} (B : BlockSystem n ℓ k)
    (E : Graph n → Tuple B → Prop) : ℝ :=
  BollobasChromatic.Main.gnpExp n (1/2) (fun G => eventProb (tupleLaw B) (E G))

noncomputable def hardExpectation {n ℓ k : ℕ} (B : BlockSystem n ℓ k)
    (f : Graph n → Tuple B → ℝ) : ℝ :=
  BollobasChromatic.Main.gnpExp n (1/2) (fun G => (tupleLaw B).mean (f G))

end DetStreamClique.MaxClique


