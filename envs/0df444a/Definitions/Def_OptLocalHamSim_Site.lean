-- Prove2me | Definitions.Def_OptLocalHamSim_Site
-- name    : OptLocalHamSim_Site
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:38.574241+00:00
-- url     : https://prove2.me/theorems/581ee150-06c8-4d3e-93d6-fdbb95b04c4f
-- title:
--   Rectangular lattice $\Lambda$, lattice metric, diameter, set distance, data and ancilla wires
-- statement:
--   Let $\Lambda\subset\mathbb Z^D$ be a finite rectangular lattice with side lengths $L_1,\dots,L_D$. Its sites are indexed as $x=(x_1,\dots,x_D)$ with $0\le x_j<L_j$. Distances are measured in the **lattice metric**
--
--   $$
--   \mathrm{dist}(x,y):=\sum_{j=1}^D|x_j-y_j| ,
--   $$
--
--   and for nonempty $X,Y\subseteq\Lambda$
--
--   $$
--   \mathrm{diam}(X):=\max_{x,x'\in X}\mathrm{dist}(x,x'),\qquad \mathrm{dist}(X,Y):=\min_{x\in X,\,y\in Y}\mathrm{dist}(x,y).
--   $$
--
--   Each site carries $q$ **data qubits**, so the system has $n=q\,|\Lambda|$ qubits. A simulation circuit additionally carries $K$ **ancillary qubits** at every site; its wires are the data qubits followed by the ancillas, and every wire sits at a site.
--
--   This is the geometry in which the paper's Hamiltonians and nearest-neighbor circuits live.
--
--   **Formalization Note** The lattice is $\{0,\dots,L_1-1\}\times\cdots\times\{0,\dots,L_D-1\}$, a translate of the paper's $\Lambda$; the metric is translation invariant. $\mathrm{diam}(\emptyset)$ and $\mathrm{dist}(X,Y)$ with an empty argument are set to $0$ and are never used on empty sets.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §1.1, p.4; §5.3, p.37

import Mathlib

namespace OptLocalHamSim

/-- The sites of a finite rectangular lattice `Λ ⊂ ℤ^D` with side lengths `L j`
(Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission, held version, sha256 44a9768a…, §1.1, p.4).

**Formalization Note** The lattice is indexed as `{0,…,L₀−1} × ⋯ × {0,…,L_{D−1}−1}`, a translate of the
paper's `Λ ⊂ ℤ^D`; the lattice metric is translation invariant, so no instance changes. -/
abbrev Site {D : ℕ} (L : Fin D → ℕ) : Type := (j : Fin D) → Fin (L j)

variable {D : ℕ} {L : Fin D → ℕ}

/-- The lattice metric `dist(x, y) := ∑_{j=1}^D |x_j − y_j|` (ℓ¹ distance), §1.1, p.4. -/
def l1dist (x y : Site L) : ℕ := ∑ j, Int.natAbs ((x j : ℤ) - (y j : ℤ))

/-- `diam(X) := max_{x,x' ∈ X} dist(x, x')`, §1.1, p.4.

**Formalization Note** On the empty set the value is `0`; the paper uses `diam` only on nonempty sets. -/
def diam (X : Finset (Site L)) : ℕ := X.sup fun x => X.sup fun y => l1dist x y

/-- `dist(X, Y) := min_{x ∈ X, y ∈ Y} dist(x, y)` for nonempty `X`, `Y`, §1.1, p.4.

**Formalization Note** When `X` or `Y` is empty the value is `0`; every statement of this mission that
uses `setDist` assumes both sets nonempty. -/
def setDist (X Y : Finset (Site L)) : ℕ :=
  if h : (X ×ˢ Y).Nonempty then (X ×ˢ Y).inf' h (fun p => l1dist p.1 p.2) else 0

/-- The data qubits: `q` qubits at every site (§1.1, p.4, "a fixed number of data qubits at each
site"). -/
abbrev Dat {D : ℕ} (L : Fin D → ℕ) (q : ℕ) : Type := Site L × Fin q

/-- The ancillary qubits: `K` ancillas at every site (§5.3, p.37, "A fixed number of ancillary qubits
per original site suffices"). -/
abbrev Anc {D : ℕ} (L : Fin D → ℕ) (K : ℕ) : Type := Site L × Fin K

/-- The wires of a simulation circuit: the data qubits followed by the ancillas. -/
abbrev Wire {D : ℕ} (L : Fin D → ℕ) (q K : ℕ) : Type := Dat L q ⊕ Anc L K

/-- The site at which a wire sits. -/
def wireSite {q K : ℕ} : Wire L q K → Site L
  | Sum.inl d => d.1
  | Sum.inr a => a.1

/-- The number of data qubits `n = q · |Λ|` ("an n-qubit lattice Hamiltonian", Problem 2, p.5). -/
def numQubits {D : ℕ} (L : Fin D → ℕ) (q : ℕ) : ℕ := q * ∏ j, L j

end OptLocalHamSim


