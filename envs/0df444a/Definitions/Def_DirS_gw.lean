-- Prove2me | Definitions.Def_DirS_gw
-- name    : DirS_gw
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T18:08:59.205056+00:00
-- url     : https://prove2.me/theorems/3f5e2d1a-4f34-4c4a-9186-320d1a49d29b
-- title:
--   The graphon layer: directed graphons, densities, and the graph world
-- statement:
--   The graphon layer of the DirS mission, carrying Section 2.2 of the paper. DirGraphon is the directed graphon interface: a (possibly asymmetric) [0,1]-valued kernel W on an abstract domain, and a finitary expectation operation exp on functionals (S -> dom) -> R for finite S, satisfying the normalization, monotonicity, linearity, Fubini, and transport axioms; no symmetry is imposed, since the kernels here are limits of directed graphs and of bipartite graphs with specified parts. DirGraphon.tIn dg B is the B-density t(B,W) of Definition 15, the expectation over the vertices of B of the product of the kernel values along the edges; DirGraphon.tInBip dg A is the bipartite A-density t_bip(A,W), integrated against the two halves of a sum type; DirGraphon.meanW dg is the mean of the kernel, the directed edge density t(K_2, W) - the modulus is kept in the statements below to match the paper's displays verbatim, though it is vacuous for the [0,1]-valued kernels of Definition 11. DirSidW B and AsymSidW A are the graphon forms of the directed and asymmetric Sidorenko properties, the right-hand sides of Propositions 21 and 22. GraphWorld is the interface connecting the finite graphs to the graphons: the directed graphon of every oriented graph and of every bipartite graph; the correspondences between the finite densities and the graphon densities (meanW against dirDens and bipDens, tIn against homDens, tInBip against bipHomDens); and the approximation schemes approx and approxB assigning to every directed graphon and every precision k finite graphs whose edge densities track the kernel mean to within 1/k and whose B- and A-densities track the graphon densities to within e(B)/k and e(A)/k.
--
--   **Formalization Note** The graph world bundles the graph-limit theory of Section 2.2 - the cut norm and distance, the compactness Theorem 13, and the counting Lemma 18 - as an interface; constructing the world from that theory is the proposed work of the mission, and the approximation axioms are what the proofs of the graphon characterizations consume.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 2.2 (Definitions 11, 14, and 15; Propositions 21 and 22; Theorems 13 and 18).

import Mathlib
import Definitions.Def_DirS_gr

/-!
# The graphon layer: directed graphons, densities, and the graph world

The graphon layer of the DirS mission, carrying the graphon side of Fox,
Himwich, Mani, and Zhou, "A note on directed analogues of the Sidorenko and
forcing conjectures" (Section 2.2): the directed graphon interface as an
abstract expectation functional over a not-necessarily-symmetric kernel;
the directed and bipartite homomorphism densities in a graphon
(Definition 15); the mean of the kernel; the graphon forms of the directed
and asymmetric Sidorenko properties; and the graph world, the interface
connecting finite graphs to graphons, bundling the graphons of the
oriented and bipartite graphs, the density correspondences, and the
approximation scheme assigning to every directed graphon a sequence of
graphs converging to it in homomorphism densities. The graph-limit theory
constructing this world - the cut norm and distance, Theorems 13 and 18
of the paper - is the proposed work of the mission.
-/

namespace DirS

/-- A directed graphon as an abstract expectation functional: a
(possibly asymmetric) [0,1]-valued kernel W on an abstract domain,
together with a finitary expectation operation satisfying the
normalization, monotonicity, linearity, Fubini, and transport axioms. No
symmetry is imposed, since the paper's kernels are limits of directed
graphs and of bipartite graphs with specified parts. -/
structure DirGraphon : Type 1 where
  dom : Type
  W : dom → dom → ℝ
  w_nonneg : ∀ x y : dom, 0 ≤ W x y
  w_le_one : ∀ x y : dom, W x y ≤ 1
  exp : (S : Type) → Fintype S → ((S → dom) → ℝ) → ℝ
  exp_one : ∀ (S : Type) (hS : Fintype S), exp S hS (fun _ => 1) = 1
  exp_mono : ∀ (S : Type) (hS : Fintype S) (f g : (S → dom) → ℝ),
      (∀ x, f x ≤ g x) → exp S hS f ≤ exp S hS g
  exp_linear : ∀ (S : Type) (hS : Fintype S) (a b : ℝ) (f g : (S → dom) → ℝ),
      exp S hS (fun x => a * f x + b * g x) = a * exp S hS f + b * exp S hS g
  exp_fubini : ∀ (S T : Type) (hS : Fintype S) (hT : Fintype T) (hST : Fintype (S ⊕ T))
      (F : ((S ⊕ T) → dom) → ℝ),
      exp (S ⊕ T) hST F = exp S hS (fun x => exp T hT (fun y => F (Sum.elim x y)))
  exp_transport : ∀ (S T : Type) (hS : Fintype S) (hT : Fintype T) (e : S ≃ T)
      (f : (T → dom) → ℝ),
      exp S hS (fun x => f (fun t => x (e.symm t))) = exp T hT f

/-- The expectation of a finitary functional over S, packaged with the
Fintype instance so that it can be applied uniformly. -/
def DirGraphon.EX (dg : DirGraphon) (S : Type) [hS : Fintype S] :
    ((S → dg.dom) → ℝ) → ℝ :=
  dg.exp S hS

/-- The B-density in the directed graphon dg, in the form of Definition 15
of the paper: the expectation over the vertices of B of the product of the
kernel values along the edges of B. -/
def DirGraphon.tIn {m : ℕ} (dg : DirGraphon) (B : OriGraph m) : ℝ :=
  dg.EX (Fin m) (fun x =>
    ∏ i : Fin m, ∏ j : Fin m, cond (B.edge i j) (dg.W (x i) (x j)) 1)

/-- The bipartite A-density in the directed graphon dg, in the form of
Definition 15 of the paper: the expectation over the two parts of A,
integrated against the two halves of a sum type, of the product of the
kernel values along the edges of A. -/
def DirGraphon.tInBip {mA nA : ℕ} (dg : DirGraphon) (A : BipGraph mA nA) : ℝ :=
  dg.EX (Fin mA ⊕ Fin nA) (fun x =>
    ∏ i : Fin mA, ∏ j : Fin nA,
      cond (A.adj i j) (dg.W (x (Sum.inl i)) (x (Sum.inr j))) 1)

/-- The mean of the kernel: the directed edge density t(K_2, W), the
expectation of W itself. -/
def DirGraphon.meanW (dg : DirGraphon) : ℝ :=
  dg.EX Bool (fun b => dg.W (b true) (b false))

/-- The graphon form of the directed Sidorenko property, the statement of
Proposition 21 of the paper: for every directed graphon, the B-density is
at least the absolute value of the mean of the kernel to the power e(B). -/
def DirSidW {m : ℕ} (B : OriGraph m) : Prop :=
  ∀ dg : DirGraphon, |dg.meanW| ^ (B.edgeCount : ℝ) ≤ dg.tIn B

/-- The graphon form of the asymmetric Sidorenko property, the statement
of Proposition 22 of the paper: for every directed graphon, the
bipartite A-density is at least the absolute value of the mean of the
kernel to the power e(A). -/
def AsymSidW {mA nA : ℕ} (A : BipGraph mA nA) : Prop :=
  ∀ dg : DirGraphon, |dg.meanW| ^ (A.bipEdgeCount : ℝ) ≤ dg.tInBip A

/-- The graph world: the interface connecting the finite oriented and
bipartite graphs to the directed graphons. It bundles the directed
graphon of every oriented graph and of every bipartite graph, the
correspondences between the finite and graphon densities, and an
approximation scheme assigning to every directed graphon and every
precision k a finite graph whose densities track the graphon's: the edge
densities to within 1/k and the B- and A-densities to within e(B)/k and
e(A)/k. Constructing this world from the graph-limit theory of Section
2.2 of the paper - the cut norm and distance, the compactness Theorem 13,
and the counting Lemma 18 - is the proposed work of the mission. -/
structure GraphWorld where
  graphonOfOri : (n : ℕ) → OriGraph n → DirGraphon
  graphonOfBip : (m n : ℕ) → BipGraph m n → DirGraphon
  wof_ori : ∀ (n : ℕ) (G : OriGraph n),
      DirGraphon.meanW (graphonOfOri n G) = G.dirDens
  wof_bip : ∀ (m n : ℕ) (H : BipGraph m n),
      DirGraphon.meanW (graphonOfBip m n H) = H.bipDens
  wof_mean : ∀ (m : ℕ) (B : OriGraph m) (n : ℕ) (G : OriGraph n),
      DirGraphon.tIn (graphonOfOri n G) B = B.homDens G
  wof_bip_mean : ∀ (mA nA : ℕ) (A : BipGraph mA nA) (m n : ℕ) (H : BipGraph m n),
      DirGraphon.tInBip (graphonOfBip m n H) A = A.bipHomDens H
  approx : ℕ → DirGraphon → Σ n : ℕ, OriGraph n
  approx_mean : ∀ (dg : DirGraphon) (k : ℕ), 0 < k →
      |OriGraph.dirDens (approx k dg).2 - dg.meanW| ≤ 1 / k
  approx_t : ∀ (dg : DirGraphon) (m : ℕ) (B : OriGraph m) (k : ℕ), 0 < k →
      |B.homDens (approx k dg).2 - dg.tIn B| ≤ (B.edgeCount : ℝ) / k
  approxB : ℕ → DirGraphon → Σ p : ℕ × ℕ, BipGraph p.1 p.2
  approxB_mean : ∀ (dg : DirGraphon) (k : ℕ), 0 < k →
      |BipGraph.bipDens (approxB k dg).2 - dg.meanW| ≤ 1 / k
  approxB_t : ∀ (dg : DirGraphon) (mA nA : ℕ) (A : BipGraph mA nA) (k : ℕ), 0 < k →
      |A.bipHomDens (approxB k dg).2 - dg.tInBip A| ≤ (A.bipEdgeCount : ℝ) / k

end DirS


