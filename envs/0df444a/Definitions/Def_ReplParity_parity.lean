-- Prove2me | Definitions.Def_ReplParity_parity
-- name    : ReplParity_parity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:28.70188+00:00
-- url     : https://prove2.me/theorems/366c050b-3aff-42e0-8fea-a5ce5c278f74
-- title:
--   Parities $f_z$, lifted examples, $e_{d+1}$ and the hyperplanes $G_z$
-- statement:
--   For $z\in\mathbb F_2^d$ the parity $f_z:\mathbb F_2^d\to\mathbb F_2$ is
--   $$f_z(x)=\langle z,x\rangle=\sum_{i} z_i x_i .$$
--   A labeled example $(x,y)$ is identified with its lifted vector $(x,y)\in\mathbb F_2^{d+1}$, whose last coordinate is the label, and $e_{d+1}=(0,\dots,0,1)$. For each $z$, the hyperplane
--   $$G_z=\{(x,\langle z,x\rangle):x\in\mathbb F_2^d\}$$
--   is the set of lifted examples that $f_z$ labels correctly.
--
--   These objects turn parity learning into a problem about spans: a sample is consistent with $f_z$ exactly when all its lifted vectors lie in $G_z$.
--
--   **Formalization Note** $G_z$ is written as the set of $v\in\mathbb F_2^{d+1}$ whose last coordinate equals $\langle z,v'\rangle$, where $v'$ is $v$ without its last coordinate; this is the same set, and it is a subspace.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

/-- **Parities, lifted examples, `e_{d+1}` and the hyperplanes `G_z`.** Shen, Zhong, *Replicable
Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission
(manuscript sha256 40424491…), §2.1, p.11 (PDF p.13): "For z ∈ 𝔽ᵈ₂ the parity f_z : 𝔽ᵈ₂ → 𝔽₂ is
f_z(x) = ⟨z, x⟩."

`parity z` is `f_z`. -/
def parity {d : ℕ} (z : Vec d) (x : Vec d) : ZMod 2 := z ⬝ᵥ x

/-- The lifted vector `(x, y) ∈ 𝔽ᵈ⁺¹₂` of a labeled example (§2.1, p.11): the label is the last
coordinate. -/
def lift {d : ℕ} (e : Example d) : Vec (d + 1) := Fin.snoc e.1 e.2

/-- `e_{d+1} = (0, …, 0, 1) ∈ 𝔽ᵈ⁺¹₂` (§2.1, p.11). -/
def eLast (d : ℕ) : Vec (d + 1) := Pi.single (Fin.last d) 1

/-- The hyperplane `G_z = {(x, ⟨z, x⟩) : x ∈ 𝔽ᵈ₂}` of `𝔽ᵈ⁺¹₂` (§2.1, p.11).

**Formalization Note.** It is written as the set of `v` whose last coordinate equals `⟨z, v'⟩`,
where `v' = Fin.init v` is `v` without its last coordinate; this is the same set. -/
def hyperplaneG {d : ℕ} (z : Vec d) : Subsp (d + 1) where
  carrier := {v | z ⬝ᵥ Fin.init v = v (Fin.last d)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    have h : (Fin.init (a + b) : Vec d) = Fin.init a + Fin.init b := rfl
    rw [h, dotProduct_add, ha, hb]
    rfl
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have h : (Fin.init (0 : Vec (d + 1)) : Vec d) = 0 := rfl
    rw [h, dotProduct_zero]
    rfl
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_ofPred_eq] at *
    have h : (Fin.init (c • v) : Vec d) = c • Fin.init v := rfl
    rw [h, dotProduct_smul, hv]
    rfl

end ReplParity


