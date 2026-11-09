-- Prove2me | Definitions.Def_CodedSorting_LocalCircuit
-- name    : CodedSorting_LocalCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:07:26.301773+00:00
-- url     : https://prove2.me/theorems/459d3aa2-8fa5-492c-afc9-7f6ae1a2e6d9
-- title:
--   The properties of the local circuit of Lemma 5.1 ($v=111$, $R=439$, $E=\mathbb Q^8$)
-- statement:
--   The local circuit has $2v+R=661$ registers with $v=111$, $R=439$: data registers $x_t,y_t$ ($t\in[v]$) and auxiliary registers $z_r$ ($r\in[R]$), and nine temporary wires; labels are subspaces of $E=\mathbb Q^8$. The target map is $(x,y,z)\mapsto(x,y+x,z)$ over $\mathbb F_2$.
--
--   For lines $\ell_t\subseteq E$, a permutation $\pi$ of $[v]$, a circuit $C$ and labels, the predicate holds when:
--
--   1. every $\ell_t$ is one-dimensional;
--   2. $C$ implements $(x,y,z)\mapsto(x,y+x,z)$ on every initial state;
--   3. the labeling is admissible (inclusion along main wires, nested temporary-wire edges);
--   4. the input and output labels are $x_t:\ \ell_t\to E$, $y_t:\ 0\to\ell_t^\perp$, $z_r:\ 0\to E$;
--   5. every temporary wire branches from a node with a seven-dimensional label, is read by at least one gate, and every gate reading it has label $0$;
--   6. from the branch point to the last gate reading the copy, the original register is not a target, and every gate on its main wire in that range carries the branch label;
--   7. the temporary wires have total length $c=9\times7=63$;
--   8. $\ell_t\perp\ell_{\pi(t)}$ for every $t$.
--
--   This predicate is the content of Lemma 5.1 and the hypothesis of Lemmas 5.2–5.3.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma 5.1, pp.11–12 (PDF 12–13)

import Mathlib
import Definitions.Def_CodedSorting_Circuit
import Definitions.Def_CodedSorting_LinAlg

namespace CodedSorting

/-! # The local circuit of Lemma 5.1

arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma 5.1, pp.11–12. -/

/-- The `2v + R = 661` registers of the local circuit, `v = 111`, `R = 439`: `inl t` is the data
register `x_t`, `inr (inl t)` is `y_t` (`t ∈ [v]`), and `inr (inr r)` is the auxiliary register `z_r`
(`r ∈ [R]`). -/
abbrev LocalReg := Fin 111 ⊕ Fin 111 ⊕ Fin 439

/-- The map `(x, y, z) ↦ (x, y + x, z)` over `𝔽₂` (Lemma 5.1, p.11). -/
def localMap (s : LocalReg → ZMod 2) : LocalReg → ZMod 2
  | .inl t => s (.inl t)
  | .inr (.inl t) => s (.inr (.inl t)) + s (.inl t)
  | .inr (.inr r) => s (.inr (.inr r))

/-- **The properties of the local circuit** (Lemma 5.1, pp.11–12), for lines `ℓ_t ⊆ E = ℚ⁸`, a
permutation `π` of `[v]`, a circuit `C` on the 661 registers with nine temporary wires, and node
labels `lab` in `E`:
1. each `ℓ_t` is one-dimensional;
2. `C` implements `(x, y, z) ↦ (x, y + x, z)` on every initial state;
3. labels grow by inclusion along main wires, and temporary-wire edges have nested endpoints;
4. input/output labels: `x_t : ℓ_t → E`, `y_t : 0 → ℓ_t^⊥`, `z_r : 0 → E`;
5. each temporary wire branches from a node with a seven-dimensional label, is read by at least one
   gate, and every gate reading it has label `0`;
6. from the branch point to the last gate reading the copy, the original register is never a
   target (it retains its value), and every gate on its main wire in that range has the branch
   label (it retains its seven-dimensional label);
7. the total length of the nine temporary wires is `c = 9 × 7 = 63`;
8. `ℓ_t ⊥ ℓ_{π(t)}` for every `t`.

**Formalization Note.** All registers in a gate share the gate's node label, which is the paper's
"At every XOR gate, all participating registers have the same subspace label". -/
def IsLocalCircuit (ℓ : Fin 111 → Submodule ℚ (Fin 8 → ℚ)) (π : Equiv.Perm (Fin 111))
    (C : XorCircuit LocalReg (Fin 9)) (lab : Node LocalReg C.G → Submodule ℚ (Fin 8 → ℚ)) :
    Prop :=
  (∀ t, Module.finrank ℚ (ℓ t) = 1) ∧
  C.Implements localMap ∧
  LabeledCircuit C lab ∧
  (∀ t, lab (.source (.inl t)) = ℓ t ∧ lab (.sink (.inl t)) = ⊤) ∧
  (∀ t, lab (.source (.inr (.inl t))) = ⊥ ∧ lab (.sink (.inr (.inl t))) = perp (ℓ t)) ∧
  (∀ r, lab (.source (.inr (.inr r))) = ⊥ ∧ lab (.sink (.inr (.inr r))) = ⊤) ∧
  (∀ k, Module.finrank ℚ (lab (C.branchNode k)) = 7) ∧
  (∀ k, ∃ j, k ∈ (C.gates j).tempOps) ∧
  (∀ k j, k ∈ (C.gates j).tempOps → lab (.gate j) = ⊥) ∧
  (∀ k j j', (C.temps k).Before j → j ≤ j' → k ∈ (C.gates j').tempOps →
    (C.gates j).target ≠ (C.temps k).reg ∧
      ((C.gates j).Involves (C.temps k).reg → lab (.gate j) = lab (C.branchNode k))) ∧
  tempLength C lab = 63 ∧
  (∀ t, ℓ t ≤ perp (ℓ (π t)))

end CodedSorting


