-- Prove2me | Definitions.Def_HSElemKernel_phiF
-- name    : HSElemKernel_phiF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:27:21.777088+00:00
-- url     : https://prove2.me/theorems/e42df58d-8b45-4cb9-837e-6b1b4530058f
-- title:
--   The formula $\Phi_{\mathcal F}$ (Section 4.3)
-- statement:
--   Let $(U, \mathcal S, k)$ be an instance, $X \subseteq U$ and $W = U \setminus X$, $\mathcal F = (\tilde h, \{g_1, \dots, g_t\})$ a two-level hash pair, $\gamma : U \to \{0,1\}^\ell$ an address map and $E$ a cardinality encoder. The formula $\Phi_{\mathcal F}$ is the conjunction of
--
--   1. $E$'s encodings of $\sum_{r=1}^{t} w_{c,r} = 1$ for every bucket $c \in [B]$ (5);
--   2. $E$'s encoding of $\sum_{x \in X} s_x + \sum_{c=1}^{B} \sum_{j=1}^{q_2} a_{c,j} \le k$ (6);
--   3. the defining clauses of $p_{c,r,j} \leftrightarrow (\neg w_{c,r} \vee a_{c,j})$ (7) and of $p^1_{c,r,j,\beta} \leftrightarrow (\neg w_{c,r} \vee z_{c,j,\beta})$, $p^0_{c,r,j,\beta} \leftrightarrow (\neg w_{c,r} \vee \neg z_{c,j,\beta})$ (8), each written as three clauses of width at most three;
--   4. for every $A \in \mathcal S$ and every local choice $\rho : C_A \to [t]$, where $C_A = \{\tilde h(v) : v \in A \cap W\}$, the CNF expansion (11) of
--   $$F_{A,\rho} = \bigvee_{x \in A \cap X} s_x \ \vee \bigvee_{v \in A \cap W} \widehat D_{\rho(\tilde h(v)),v}, \qquad \widehat D_{r,v} = p_{c,r,j} \wedge \bigwedge_{\beta=1}^{\ell} p^{\gamma(v)_\beta}_{c,r,j,\beta}\ \ (c = \tilde h(v),\ j = g_r(v)), \tag{10}$$
--   that is, all clauses keeping every $s_x$, $x \in A \cap X$, and one literal of $\widehat D_{\rho(\tilde h(v)),v}$ for each $v \in A \cap W$.
--
--   $\Phi_{\mathcal F}$ is the randomized encoding of Lemma 2.2 once $X$ is the union of a maximal packing and $\mathcal F$ is sampled by Lemma 4.2.
--
--   **Formalization Note** $\Phi_{\mathcal F}$ is a published `MantriCVQ.CNF` over the variable set of Table 2. The order in which clauses are listed (sets of $\mathcal S$, elements, local maps, the constrained variables of (6)) is fixed by a choice and changes neither satisfiability nor any count.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Sections 4.2–4.3, Eqs. (5)–(11), pp.10–12

import Mathlib
import Definitions.Def_HSElemKernel_PhiVar

namespace HSElemKernel

/-- The clauses of `p ↔ (¬w ∨ l)` for a literal `l = (u, b)`:
`(¬p ∨ ¬w ∨ l)`, `(w ∨ p)`, `(¬l ∨ p)`. (Helper of `phiF`.) -/
def iffNotOrClauses {V : Type} (p w : V) (l : V × Bool) : List (List (V × Bool)) :=
  [[(p, false), (w, false), l], [(w, true), (p, true)], [(l.1, !l.2), (p, true)]]

open PhiVar in
/-- The formula `Φ_F` (Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…,
Sections 4.2–4.3, pp.10–12) of an instance `(Fin n, S, k)`, a set `X ⊆ U` (with `W = U \ X`),
a pair `F = (h̃, H₂)`, an address map `γ : U → {0,1}^ℓ` and a cardinality encoder `E`: the
conjunction of
1. the encodings by `E` of `∑_{r ∈ [t]} w_{c,r} = 1` for every `c ∈ [B]` (5), each with its own
   auxiliary variables;
2. the encoding by `E` of `∑_{x ∈ X} s_x + ∑_{c,j} a_{c,j} ≤ k` (6);
3. the defining clauses of `p_{c,r,j} ↔ (¬w_{c,r} ∨ a_{c,j})` (7) and of
   `p^1_{c,r,j,β} ↔ (¬w_{c,r} ∨ z_{c,j,β})`, `p^0_{c,r,j,β} ↔ (¬w_{c,r} ∨ ¬z_{c,j,β})` (8);
4. for every `A ∈ S` and every local map `ρ : C_A → [t]`, `C_A = h̃(A ∩ W)`, the CNF expansion
   (11) of `F_{A,ρ} = ⋁_{x ∈ A∩X} s_x ∨ ⋁_{v ∈ A∩W} D̂_{ρ(h̃(v)),v}` (10), where
   `D̂_{r,v} = p_{c,r,j} ∧ ⋀_β p^{γ(v)_β}_{c,r,j,β}` with `c = h̃(v)`, `j = g_r(v)` (9): every
   clause keeps all `s_x` (`x ∈ A ∩ X`) and one literal of `D̂_{ρ(h̃(v)),v}` for each
   `v ∈ A ∩ W`.

**Formalization Note** The formula is a published `MantriCVQ.CNF` over `PhiVar E X F ℓ k`. The constrained variables of (6)
are listed as `s_x` in the order of `X.equivFin`, then `a_{c,j}` in the order of
`finProdFinEquiv`; the sets of `S`, the elements of a set and the local maps are listed by
`Finset.toList`. These orders change neither satisfiability nor any count. -/
noncomputable def phiF {n : ℕ} (E : CardEncoder) (S : Finset (Finset (Fin n))) (k : ℕ)
    (X : Finset (Fin n)) (F : TwoLevelHash (Fin n)) {ℓ : ℕ} (γ : Fin n → Fin ℓ → Bool) :
    MantriCVQ.CNF (PhiVar E X F ℓ k) :=
  let card5 : List (List (PhiVar E X F ℓ k × Bool)) :=
    (List.finRange F.B).flatMap fun c =>
      (E.enc F.t 1 .eq).map (List.map fun l => (Sum.elim (vW c) (vAux5 c) l.1, l.2))
  let xs6 : Fin (X.card + F.B * F.q2) → PhiVar E X F ℓ k :=
    Fin.addCases (fun i => vS (X.equivFin.symm i))
      (fun j => vA (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  let card6 : List (List (PhiVar E X F ℓ k × Bool)) :=
    (E.enc (X.card + F.B * F.q2) k .le).map (List.map fun l => (Sum.elim xs6 vAux6 l.1, l.2))
  let def7 : List (List (PhiVar E X F ℓ k × Bool)) :=
    (List.finRange F.B).flatMap fun c => (List.finRange F.t).flatMap fun r =>
      (List.finRange F.q2).flatMap fun j => iffNotOrClauses (vP c r j) (vW c r) (vA c j, true)
  let def8 : List (List (PhiVar E X F ℓ k × Bool)) :=
    (List.finRange F.B).flatMap fun c => (List.finRange F.t).flatMap fun r =>
      (List.finRange F.q2).flatMap fun j => (List.finRange ℓ).flatMap fun β =>
        [true, false].flatMap fun b =>
          iffNotOrClauses (vPb c r j β b) (vW c r) (vZ c j β, b)
  let hit : List (List (PhiVar E X F ℓ k × Bool)) :=
    S.toList.flatMap fun A =>
      (Finset.univ : Finset ({c // c ∈ (A \ X).image F.h} → Fin F.t)).toList.flatMap fun ρ =>
        let sLits : List (PhiVar E X F ℓ k × Bool) :=
          (A ∩ X).attach.toList.map fun x =>
            (vS ⟨x.1, (Finset.mem_inter.1 x.2).2⟩, true)
        let dHat : List (List (PhiVar E X F ℓ k × Bool)) :=
          (A \ X).attach.toList.map fun v =>
            let c := F.h v.1
            let r := ρ ⟨c, Finset.mem_image_of_mem F.h v.2⟩
            let j := F.g r v.1
            (vP c r j, true) :: List.ofFn (fun β => (vPb c r j β (γ v.1 β), true))
        dHat.sections.map (fun sec => sLits ++ sec)
  card5 ++ card6 ++ def7 ++ def8 ++ hit

end HSElemKernel


