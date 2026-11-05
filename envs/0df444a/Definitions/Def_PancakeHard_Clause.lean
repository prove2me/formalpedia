-- Prove2me | Definitions.Def_PancakeHard_Clause
-- name    : PancakeHard_Clause
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:45.969212+00:00
-- url     : https://prove2.me/theorems/bda81bcc-1952-4b7c-843d-aadf82bac937
-- title:
--   Definition 7 — the clause gadget $Clause(a,b,c,p)=(\gamma,\Gamma,\Delta)$ with $\Gamma^1,\Gamma^2,\Gamma^3$
-- statement:
--   Let $p_\Lambda$ and $m$ be fixed, with tests $test_j$ from $Literals(p_\Lambda,m)$. For pairwise distinct $a,b,c\in\llbracket 1;m\rrbracket$ and an integer $p$, let $(E_1,F_1)=Fork(p+2)$, $(E_2,F_2)=Fork(p+45)$, $(take_1,put_1,G_1,H_1)=Hook(p+21)$, $(take_2,put_2,G_2,H_2)=Hook(p+33)$, $D_1=Dock(p+2,p+17)$ and $D_2=Dock(p+21,p+60)$. Then $Clause(a,b,c,p)=(\gamma,\Gamma,\Delta)$ with $\gamma=take_1$, $\Delta=\langle D_1,D_2\rangle$,
--   $$\Gamma=\langle G_1,E_1,take_2,put_1,test_c,F_1,G_2,E_2,test_a,put_2,test_b,F_2,H_2,H_1\rangle,$$
--   and
--   $$\Gamma^1=\langle G_1'',test_c,F_1^1,G_2'',test_b,F_2^1,H_2'',H_1''\rangle,\quad \Gamma^2=\langle G_1'',test_c,F_1^1,G_2'',test_a,F_2^2,H_2'',H_1''\rangle,$$
--   $$\Gamma^3=\langle G_1'',take_2,F_1^2,G_2,E_2,test_a,put_2,test_b,F_2,H_2,H_1''\rangle .$$
--
--   The gadget checks one clause $\lambda_a\vee\lambda_b\vee\lambda_c$: every efficient path through it must test an open lock among $a$, $b$, $c$ (Properties 10 and 11).
--
--   **Formalization Note** The components are `clauseGamma p`, `clauseΓ pΛ a b c p`, `clauseΔ p`, `clauseΓ1 pΛ b c p`, `clauseΓ2 pΛ a c p`, `clauseΓ3 pΛ a b p` (each takes only the indices it uses); the condition on $a,b,c$ is a hypothesis of the statements that use the gadget.
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.2.3, p.16, Definition 7

import Mathlib
import Definitions.Def_PancakeHard_Dock
import Definitions.Def_PancakeHard_Hook
import Definitions.Def_PancakeHard_Fork
import Definitions.Def_PancakeHard_Literals

set_option autoImplicit false

namespace PancakeHard

/-- `γ` of `Clause(a, b, c, p)` (Definition 7, arXiv:1111.0434v2, §3.2.3, p.16):
`(take₁, put₁, G₁, H₁) = Hook(p + 21)` and `γ = take₁`.

**Formalization Note** The page's `p` is an integer, and here it is one (`p : ℤ`): the least entry of
`γ`, `Γ` is `p + 3`, so `p = −2` and `p = −1` occur in stacks (Property 10), while `Δ` contains `p + 1`.
Every offset is written `(p + c).toNat`, which is the page's `p + c` for `p ≥ −2`, the only offsets for
which the gadget has positive entries. -/
def clauseGamma (p : ℤ) : ℕ := hookTake (p + 21).toNat

/-- `Γ` of `Clause(a, b, c, p)` (Definition 7, p.16), for fixed `p_Λ`:
`Γ = ⟨G₁, E₁, take₂, put₁, test_c, F₁, G₂, E₂, test_a, put₂, test_b, F₂, H₂, H₁⟩` where
`(E₁, F₁) = Fork(p + 2)`, `(E₂, F₂) = Fork(p + 45)`, `(take₁, put₁, G₁, H₁) = Hook(p + 21)`,
`(take₂, put₂, G₂, H₂) = Hook(p + 33)` and `test_j` are the tests of `Literals(p_Λ, m)`.

**Formalization Note** The paper requires `a, b, c ∈ ⟦1 ; m⟧` pairwise distinct; the statements
using the gadget carry that hypothesis. -/
def clauseΓ (pΛ a b c : ℕ) (p : ℤ) : List ℕ :=
  hookG (p + 21).toNat ++ forkE (p + 2).toNat ++ [hookTake (p + 33).toNat, hookPut (p + 21).toNat, litTest pΛ c] ++
    forkF (p + 2).toNat ++ hookG (p + 33).toNat ++ forkE (p + 45).toNat ++
    [litTest pΛ a, hookPut (p + 33).toNat, litTest pΛ b] ++ forkF (p + 45).toNat ++ hookH (p + 33).toNat ++
    hookH (p + 21).toNat

/-- `Δ` of `Clause(a, b, c, p)` (Definition 7, p.16): `Δ = ⟨D₁, D₂⟩` with
`D₁ = Dock(p + 2, p + 17)` and `D₂ = Dock(p + 21, p + 60)`. -/
def clauseΔ (p : ℤ) : List ℕ := Dock (p + 2).toNat (p + 17).toNat ++ Dock (p + 21).toNat (p + 60).toNat

/-- `Γ¹` (Definition 7, p.16): `Γ¹ = ⟨G₁″, test_c, F₁¹, G₂″, test_b, F₂¹, H₂″, H₁″⟩`. -/
def clauseΓ1 (pΛ b c : ℕ) (p : ℤ) : List ℕ :=
  hookG'' (p + 21).toNat ++ [litTest pΛ c] ++ forkF1 (p + 2).toNat ++ hookG'' (p + 33).toNat ++ [litTest pΛ b] ++
    forkF1 (p + 45).toNat ++ hookH'' (p + 33).toNat ++ hookH'' (p + 21).toNat

/-- `Γ²` (Definition 7, p.16): `Γ² = ⟨G₁″, test_c, F₁¹, G₂″, test_a, F₂², H₂″, H₁″⟩`. -/
def clauseΓ2 (pΛ a c : ℕ) (p : ℤ) : List ℕ :=
  hookG'' (p + 21).toNat ++ [litTest pΛ c] ++ forkF1 (p + 2).toNat ++ hookG'' (p + 33).toNat ++ [litTest pΛ a] ++
    forkF2 (p + 45).toNat ++ hookH'' (p + 33).toNat ++ hookH'' (p + 21).toNat

/-- `Γ³` (Definition 7, p.16):
`Γ³ = ⟨G₁″, take₂, F₁², G₂, E₂, test_a, put₂, test_b, F₂, H₂, H₁″⟩`. -/
def clauseΓ3 (pΛ a b : ℕ) (p : ℤ) : List ℕ :=
  hookG'' (p + 21).toNat ++ [hookTake (p + 33).toNat] ++ forkF2 (p + 2).toNat ++ hookG (p + 33).toNat ++ forkE (p + 45).toNat ++
    [litTest pΛ a, hookPut (p + 33).toNat, litTest pΛ b] ++ forkF (p + 45).toNat ++ hookH (p + 33).toNat ++
    hookH'' (p + 21).toNat

end PancakeHard


