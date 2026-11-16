-- Prove2me | Definitions.Def_QPSpinProfile_Supplement_Circ
-- name    : QPSpinProfile_Supplement_Circ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:32:07.013223+00:00
-- url     : https://prove2.me/theorems/496824c4-8b45-461e-b73c-5ad5e202407b
-- title:
--   Shallow circuits $\mathrm{Circ}[D]_M$ of one- and two-qubit gates (Definition 3.7)
-- statement:
--   For integers $M$ and $D \ge 0$, $\mathrm{Circ}[D]_M$ is the class of $M$-qubit circuits of **depth at most $D$**, where every layer consists of one- and two-qubit gates with pairwise disjoint supports.
--
--   Precisely, a **gate** is a set $S$ of one or two qubits together with an arbitrary unitary $U$ on $(\mathbb C^2)^{\otimes S}$; it acts on all $M$ qubits as $U \otimes I$, i.e. as $U$ on $S$ and as the identity elsewhere. A **layer** is a collection of gates whose supports are pairwise disjoint, and its unitary is the product of its gates. A circuit is a product
--   $$
--   Q = L_k L_{k-1} \cdots L_1, \qquad k \le D,
--   $$
--   of layer unitaries. No gate set and no geometric locality are imposed: a two-qubit gate may act on any two qubits.
--
--   Definition 4.11 calls these circuits "depth-$D$ matching circuits"; Proposition 4.14 and Lemma 4.15 of the paper read them as matching circuits of depth at most $D$.
--
--   **Formalization Note** A circuit is a list of at most $D$ layers, each a list of gates with pairwise disjoint supports. Empty layers and the empty circuit give the identity, so "depth at most $D$" and "depth exactly $D$ with identity layers" are the same class.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Definition 3.7, p.39 (PDF p.42); Definition 4.11, p.59 (PDF p.62)

import Mathlib
import Definitions.Def_QPSpinProfile_PauliString

namespace QPSpinProfile.Supplement

open Matrix

/-- A one- or two-qubit gate on `M` qubits: a support `supp ⊆ Fin M` of one or two qubits
and an arbitrary unitary `U` on the qubits of `supp` (Al-Ghattas, Gamarnik, Kiani, *Beyond light
cones*, arXiv:2610.02166, held version sha256 a0a1ec89…, Definition 3.7, p.39, PDF p.42). No gate
set and no geometric locality are imposed. -/
structure Gate (M : ℕ) where
  /-- The qubits the gate acts on. -/
  supp : Finset (Fin M)
  /-- One- or two-qubit gate. -/
  card_supp : supp.card = 1 ∨ supp.card = 2
  /-- The gate's matrix on the qubits of `supp`. -/
  U : Matrix (supp → Fin 2) (supp → Fin 2) ℂ
  /-- The gate is unitary. -/
  unitary : U ∈ Matrix.unitaryGroup (supp → Fin 2) ℂ

open Classical in
/-- The `2^M × 2^M` matrix `U ⊗ I` of a gate: it acts as `U` on the qubits of its support and as
the identity on the others (arXiv:2610.02166, Definition 3.7, p.39, PDF p.42). -/
noncomputable def Gate.mat {M : ℕ} (G : Gate M) : Matrix (Qubits M) (Qubits M) ℂ :=
  Matrix.of fun x y =>
    if ∀ i, i ∉ G.supp → x i = y i then G.U (fun i => x i.1) (fun i => y i.1) else 0

/-- A layer: a list of gates with pairwise disjoint supports (arXiv:2610.02166, Definition 3.7,
p.39, PDF p.42). -/
def IsLayer {M : ℕ} (L : List (Gate M)) : Prop :=
  L.Pairwise fun G H => Disjoint G.supp H.supp

/-- The unitary of a layer: the product of its gates' matrices (they act on disjoint qubits and
commute, so the order is immaterial). -/
noncomputable def layerMat {M : ℕ} (L : List (Gate M)) : Matrix (Qubits M) (Qubits M) ℂ :=
  (L.map Gate.mat).prod

/-- `Circ[D]_M`, Definition 3.7 (arXiv:2610.02166, held version sha256 a0a1ec89…, p.39, PDF p.42):
the `M`-qubit circuits of depth at most `D`, where every layer consists of one- and two-qubit gates
with pairwise disjoint supports. Definition 4.11 calls these "depth-`D` matching circuits"
(read as depth at most `D`, as in Proposition 4.14, p.62, and Lemma 4.15, p.64).

**Formalization Note** A circuit is a list of at most `D` layers and its unitary is the product of
the layer unitaries; an empty layer or an empty list gives the identity, so "depth at most `D`" and
"depth exactly `D` with identity layers allowed" give the same set. -/
def Circ (D M : ℕ) : Set (Matrix (Qubits M) (Qubits M) ℂ) :=
  {Q | ∃ Ls : List (List (Gate M)), Ls.length ≤ D ∧ (∀ L ∈ Ls, IsLayer L) ∧
    Q = (Ls.map layerMat).prod}

end QPSpinProfile.Supplement


