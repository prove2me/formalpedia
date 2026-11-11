-- Prove2me | Definitions.Def_LindbladShallow_Circuit
-- name    : LindbladShallow_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:19:39.06185+00:00
-- url     : https://prove2.me/theorems/7fed4f29-b5b5-4685-9708-cb4c8c6e5c99
-- title:
--   Segmented nearest-neighbour circuits over the gate set $\mathcal G$ of Eq. (68), and their resource counts
-- statement:
--   The **gate set** is the inverse-closed alphabet
--   $$\mathcal G=\{H,X,Z,S,S^\dagger,T,T^\dagger,CX,A_x,A_x^\dagger,A_z,A_z^\dagger\},\qquad A_p=(3I-4i\sigma_p)/5,$$
--   with $H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $S=\mathrm{diag}(1,i)$, $T=\mathrm{diag}(1,e^{i\pi/4})$ and the ordered CNOT $CX|a,b\rangle=|a,a\oplus b\rangle$.
--
--   A **circuit description** consists of a refinement factor $f$, offsets $u_k\in\{0,\dots,f-1\}^D$ (system qubit $k$ of site $x$ sits at $f x+u_k$) and a list of **segments**; each segment lists the positions of its auxiliary qubits and a list of layers of gates placed at positions of $\mathbb Z^D$. It is **well formed** if $f\ge1$, $k\mapsto u_k$ is injective, each segment's auxiliary positions are distinct and avoid the system positions, every gate acts on positions of its segment, every CX acts on two distinct positions at $\ell^1$ distance $1$, and the gates of a layer act on disjoint wires.
--
--   The resources are: $G$ = total number of gates; $d_{NN}$ = total number of layers; $Q_{\mathrm{peak}}=n d_0+\max_s|\mathrm{aux}_s|$; $N_{\mathrm{fresh}}=\sum_s|\mathrm{aux}_s|$.
--
--   This is the circuit model of p.10 and Eq. (68), in which the resource bounds of Theorem 2.1 are counted.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), p.10; §5.5, p.47; Eq. (68), pp.69–70

import Mathlib
import Definitions.Def_LindbladShallow_Instance

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The one-qubit symbols of the fixed inverse-closed alphabet
`G := {H, X, Z, S, S†, T, T†, CX, A_x, A_x†, A_z, A_z†}` (arXiv:2610.05362, held version
sha256 8f4637ef…, Eq. (68), p.69). `CX` is the only two-qubit symbol and is the constructor
`Gate.cx`. -/
inductive GateName
  | H | X | Z | S | Sdg | T | Tdg | Ax | Axdg | Az | Azdg
  deriving DecidableEq

/-- `A_p := (3I − 4iσ_p)/5` (Eq. (68)); `A_x`, `A_z`. -/
noncomputable def matA (σp : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 5 : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (4 * Complex.I) • σp)

/-- The 2×2 matrix of a one-qubit symbol in the basis `|0⟩, |1⟩` (Eq. (68), p.69):
`H = (1/√2)[[1,1],[1,−1]]`, `X = σ_x`, `Z = σ_z`, `S = diag(1, i)`, `T = diag(1, e^{iπ/4})`,
`A_p = (3I − 4iσ_p)/5`, and the adjoints `S†`, `T†`, `A_p†`. -/
noncomputable def GateName.mat : GateName → Matrix (Fin 2) (Fin 2) ℂ
  | .H => (1 / (Real.sqrt 2 : ℂ)) • !![1, 1; 1, -1]
  | .X => !![0, 1; 1, 0]
  | .Z => !![1, 0; 0, -1]
  | .S => !![1, 0; 0, Complex.I]
  | .Sdg => !![1, 0; 0, -Complex.I]
  | .T => !![1, 0; 0, Complex.exp (Complex.I * (Real.pi / 4 : ℝ))]
  | .Tdg => !![1, 0; 0, Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ)))]
  | .Ax => matA !![0, 1; 1, 0]
  | .Axdg => (matA !![0, 1; 1, 0])ᴴ
  | .Az => matA !![1, 0; 0, -1]
  | .Azdg => (matA !![1, 0; 0, -1])ᴴ

/-- A gate of the output circuit, placed at lattice positions of the refinement (points of
`ℤ^D`): a one-qubit symbol at position `p`, or the ordered CNOT `CX|a, b⟩ = |a, a ⊕ b⟩` with control
at `c` and target at `t` (Eq. (68), p.69–70; "either orientation on an adjacent pair is
allowed"). -/
inductive Gate (D : ℕ)
  | one (g : GateName) (p : Fin D → ℤ)
  | cx (c t : Fin D → ℤ)

/-- The positions (wires) a gate acts on. -/
def Gate.wires {D : ℕ} : Gate D → List (Fin D → ℤ)
  | .one _ p => [p]
  | .cx c t => [c, t]

/-- One segment of the output circuit (arXiv:2610.05362, p.10 and Eq. (47), p.50): it allocates
the auxiliary qubits at the listed positions, initialized to `|0⟩`, applies its layers in order
(head first; each layer is a list of gates on disjoint wires), and then discards the
auxiliaries. -/
structure Segment (D : ℕ) where
  aux : List (Fin D → ℤ)
  layers : List (List (Gate D))

/-- A circuit description (arXiv:2610.05362, p.10; §5.5, p.47): the refinement factor `f`, the
offsets `u k ∈ {0, …, f−1}^D` of the `d0` system qubits in the refinement cell of a site (system
qubit `(x, k)` sits at `f·x + u_k`), and the list of segments, executed in order. -/
structure Circuit (P : Params) where
  f : ℕ
  u : Fin P.d0 → Fin P.D → ℕ
  segs : List (Segment P.D)

/-- The position `f·x + u_k` of system qubit `k` of site `x = Λ[j]` (p.47). -/
def sysPos {P : Params} (I : Instance P) (c : Circuit P) (j : Fin I.n) (k : Fin P.d0) :
    Fin P.D → ℤ :=
  fun i => (c.f : ℤ) * I.sites.get j i + (c.u k i : ℤ)

/-- ℓ¹ distance on `ℤ^D`. -/
def l1dist {D : ℕ} (p q : Fin D → ℤ) : ℕ :=
  ∑ i, (p i - q i).natAbs

/-- The positions of segment `s`: all system positions and its auxiliary positions. -/
def segPositions {P : Params} (I : Instance P) (c : Circuit P) (s : Segment P.D) :
    Set (Fin P.D → ℤ) :=
  {p | (∃ j k, sysPos I c j k = p) ∨ p ∈ s.aux}

/-- Well-formedness of a circuit description for input `I` (arXiv:2610.05362, p.10, Eq. (68),
§5.5):
1. `f ≥ 1`, each offset `u_k ∈ {0, …, f−1}^D`, and `k ↦ u_k` is injective (so distinct system
   qubits sit at distinct positions of the refinement);
2. in every segment, the auxiliary positions are distinct and differ from all system positions;
3. every gate acts on positions of its segment;
4. every CX has distinct control and target at ℓ¹ distance exactly `1` (nearest neighbours of the
   grid `ℤ^D`);
5. the gates of a layer act on pairwise disjoint wires. -/
def Circuit.WellFormed {P : Params} (I : Instance P) (c : Circuit P) : Prop :=
  1 ≤ c.f ∧ (∀ k i, c.u k i < c.f) ∧ Function.Injective c.u ∧
  ∀ s ∈ c.segs, s.aux.Nodup ∧ (∀ a ∈ s.aux, ∀ j k, sysPos I c j k ≠ a) ∧
    ∀ L ∈ s.layers,
      (∀ g ∈ L, ∀ p ∈ g.wires, p ∈ segPositions I c s) ∧
      (∀ g ∈ L, ∀ a b, g = .cx a b → a ≠ b ∧ l1dist a b = 1) ∧
      L.Pairwise (fun g g' => ∀ p ∈ g.wires, p ∉ g'.wires)

/-- The gate count `G`: every occurrence of a one- or two-qubit gate (p.10). -/
def Circuit.gateCount {P : Params} (c : Circuit P) : ℕ :=
  (c.segs.map fun s => (s.layers.map List.length).sum).sum

/-- The nearest-neighbour depth `d_NN`: the number of layers of gates on disjoint wires, over all
segments (p.10). -/
def Circuit.depth {P : Params} (c : Circuit P) : ℕ :=
  (c.segs.map fun s => s.layers.length).sum

/-- The peak qubit count `Q_peak`: the `n·d0` system qubits plus the largest auxiliary allocation of
a segment (p.10; auxiliaries are allocated and discarded at segment boundaries). -/
def Circuit.peakQubits {P : Params} (I : Instance P) (c : Circuit P) : ℕ :=
  I.n * P.d0 + (c.segs.map fun s => s.aux.length).foldr max 0

/-- The number `N_fresh` of auxiliary-qubit initializations, over all segments (p.10). -/
def Circuit.freshInits {P : Params} (c : Circuit P) : ℕ :=
  (c.segs.map fun s => s.aux.length).sum

end LindbladShallow


