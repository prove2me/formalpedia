-- Prove2me | Definitions.Def_AlgebraicPCSP_Colouring_Structures
-- name    : AlgebraicPCSP_Colouring_Structures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:31.851896+00:00
-- url     : https://prove2.me/theorems/a6218487-6936-4e37-9770-435276b7a5ab
-- title:
--   K_k, H_k, the minion 𝓗_K = Pol(H₂, H_K) and Olšák functions (Examples 2.9, 2.11, Definition 6.1)
-- statement:
--   This module fixes the concrete templates and the Olšák identities of §2.1 and §6.1. Write $E_k = \{0, 1, \dots, k-1\}$.
--
--   1. **Complete graphs** (Example 2.9). $\mathbf K_k = (E_k; \neq_k)$ with the binary relation $\neq_k = \{(a, b) \in E_k^2 \mid a \neq b\}$. The $n$-ary members of $\mathrm{Pol}(\mathbf K_k, \mathbf K_c)$ are exactly the $c$-colourings of the $n$-th power $\mathbf K_k^n$.
--   2. **Hypergraph templates** (Example 2.11). $\mathbf H_k = (E_k; \mathrm{NAE}_k)$ with the ternary "not-all-equal" relation
--   $$
--   \mathrm{NAE}_k = E_k^3 \setminus \{(a, a, a) \mid a \in E_k\}.
--   $$
--   3. For $k \le c$, the inclusion $E_k \subseteq E_c$ is a homomorphism $\mathbf K_k \to \mathbf K_c$ and $\mathbf H_k \to \mathbf H_c$, so both pairs are PCSP templates.
--   4. **The minion $\mathscr H_K$** (p. 37): $\mathscr H_K = \mathrm{Pol}(\mathbf H_2, \mathbf H_K)$ for $K \ge 2$.
--   5. **Olšák functions** (Definition 6.1). A 6-ary function $o$ is an *Olšák function* if
--   $$
--   o(x, x, y, y, y, x) \approx o(x, y, x, y, x, y) \approx o(y, x, x, x, y, y),
--   $$
--   that is, the three values coincide for all $x, y$ in the domain. A minion *contains an Olšák function* if one of its 6-ary members is one.
--
--   Approximate graph colouring is $\mathrm{PCSP}(\mathbf K_k, \mathbf K_c)$ and approximate hypergraph colouring is $\mathrm{PCSP}(\mathbf H_k, \mathbf H_c)$; the Olšák identities are the single obstruction that separates them in the mission's goal.
--
--   **Formalization Note** $E_k$ is `Fin k`. Each structure has a one-symbol signature (`Unit`) of arity 2 or 3. The two template facts are small lemmas inside this definition file because `Pol` needs a homomorphism witness. The Olšák identities are imposed for all $x, y$, including $x = y$.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 10 Example 2.9, p. 11 Example 2.11, p. 37 (𝓗_k = Pol(H₂, H_k)) and Definition 6.1

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion

namespace AlgebraicPCSP.Colouring

open PCSPBLPAff.Symmetric

/-- The complete graph `K_k = (E_k; ≠_k)` (Example 2.9, arXiv:1811.00970v3, p. 10): domain
`E_k = {0, …, k − 1}` (as `Fin k`) and one binary relation `≠_k = {(a, b) ∈ E_k² | a ≠ b}`.
The signature has a single symbol (`Unit`) of arity 2. -/
def Kgraph (k : ℕ) : RelStruct Unit (fun _ => 2) (Fin k) where
  rel _ := {t : Fin 2 → Fin k | t 0 ≠ t 1}

/-- The 3-uniform hypergraph structure `H_k = (E_k; NAE_k)` (Example 2.11, p. 11): domain
`E_k` (as `Fin k`) and one ternary relation `NAE_k = E_k³ ∖ {(a, a, a) | a ∈ E_k}`, the
"not-all-equal" triples. The signature has a single symbol (`Unit`) of arity 3. -/
def Hgraph (k : ℕ) : RelStruct Unit (fun _ => 3) (Fin k) where
  rel _ := {t : Fin 3 → Fin k | ¬ (t 0 = t 1 ∧ t 1 = t 2)}

/-- For `k ≤ c`, `(K_k, K_c)` is a PCSP template: the inclusion `E_k → E_c` is a
homomorphism `K_k → K_c` (Example 2.9). -/
theorem Kgraph_template {k c : ℕ} (h : k ≤ c) : IsPromiseTemplate (Kgraph k) (Kgraph c) := by
  refine ⟨Fin.castLE h, ?_⟩
  intro R t ht
  simp only [Kgraph, Set.mem_ofPred_eq, Function.comp_apply] at ht ⊢
  intro he
  exact ht (Fin.castLE_injective h he)

/-- For `k ≤ c`, `(H_k, H_c)` is a PCSP template: the inclusion `E_k → E_c` is a
homomorphism `H_k → H_c` (Example 2.11). -/
theorem Hgraph_template {k c : ℕ} (h : k ≤ c) : IsPromiseTemplate (Hgraph k) (Hgraph c) := by
  refine ⟨Fin.castLE h, ?_⟩
  intro R t ht
  simp only [Hgraph, Set.mem_ofPred_eq, Function.comp_apply] at ht ⊢
  rintro ⟨h01, h12⟩
  exact ht ⟨Fin.castLE_injective h h01, Fin.castLE_injective h h12⟩

/-- The minion `𝓗_K = Pol(H₂, H_K)` (p. 37), for `K ≥ 2`. -/
def HMinion (K : ℕ) (hK : 2 ≤ K) : Minion (Fin 2) (Fin K) :=
  Pol (Hgraph 2) (Hgraph K) (Hgraph_template hK)

/-- An Olšák function (Definition 6.1, p. 37): a 6-ary function `o` satisfying
`o(x, x, y, y, y, x) ≈ o(x, y, x, y, x, y) ≈ o(y, x, x, x, y, y)`, i.e. the three values are
equal for all `x, y` in the domain. -/
def IsOlsak {A B : Type} (o : (Fin 6 → A) → B) : Prop :=
  ∀ x y : A, o ![x, x, y, y, y, x] = o ![x, y, x, y, x, y] ∧
    o ![x, y, x, y, x, y] = o ![y, x, x, x, y, y]

/-- The minion `M` contains an Olšák function: some 6-ary member of `M` is an Olšák
function. -/
def ContainsOlsak {A B : Type} (M : Minion A B) : Prop :=
  ∃ o ∈ M.mem 6, IsOlsak o

end AlgebraicPCSP.Colouring


