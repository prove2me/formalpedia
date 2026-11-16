-- Prove2me | Definitions.Def_SwitchingStable_Universal_Supplement_Certificate
-- name    : SwitchingStable_Universal_Supplement_Certificate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:34:44.041005+00:00
-- url     : https://prove2.me/theorems/3799ffb0-90cc-4a13-b9db-d72ae48e9532
-- title:
--   Finite boundary certificates and half-open interval endpoints
-- statement:
--   Let $m$ be the number of coordinates. Each coordinate $i$ has a positive integer domain size $d_i$, and $F$ is a finite family of vectors $z$ with $0\le z_i<d_i$. At every boundary $1\le j<d_i$, the set $W_{i,j}(z)$ contains coordinates other than $i$. Validity means
--
--   $$p\in W_{i,j}(z),\ z'\in F,\ z'_p=z_p\quad\Longrightarrow\quad (z'_i\ge j\ \Longleftrightarrow\ z_i\ge j).$$
--
--   For a predecessor set $P$ excluding $i$, put $q=z_i$ and define
--
--   $$L_i(z,P)=\max(\{0\}\cup\{j:1\le j\le q,\ W_{i,j}(z)\cap P\ne\varnothing\}),$$
--   $$R_i(z,P)=\min(\{d_i\}\cup\{j:q<j<d_i,\ W_{i,j}(z)\cap P\ne\varnothing\}).$$
--
--   The length is the real number $R_i-L_i$. A valid vector has $L_i\le q<R_i$. This general object serves both stable-index families and the abstract construction of Appendix I.
--
--   **Formalization Note** Raw certificate data and their validity predicate are separate. Validity asserts positive heterogeneous domains, membership in those domains, exclusion of self witnesses, and precisely the displayed implication. The lower and upper sentinels are $0$ and $d_i$.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 35, PDF p. 36, Appendix H, boundary-certificate system and endpoints

import Mathlib

namespace SwitchingStable.Universal.Supplement

/-- Appendix H's general finite, heterogeneous boundary-certificate data. -/
structure Certificate (m : ℕ) where
  d : Fin m → ℕ
  family : Finset (Fin m → ℕ)
  witnesses : (Fin m → ℕ) → Fin m → ℕ → Finset (Fin m)

variable {m : ℕ}

/-- Validity includes exactly positive domains and the threshold certificate implication. -/
def Certificate.Valid (B : Certificate m) : Prop :=
  (∀ i, 0 < B.d i) ∧
  (∀ z ∈ B.family, ∀ i, z i < B.d i) ∧
  ∀ z ∈ B.family, ∀ i j, 1 ≤ j → j < B.d i →
    i ∉ B.witnesses z i j ∧
    ∀ p ∈ B.witnesses z i j, ∀ z' ∈ B.family,
      z' p = z p → (j ≤ z' i ↔ j ≤ z i)

noncomputable def Certificate.lower (B : Certificate m) (z : Fin m → ℕ)
    (i : Fin m) (P : Finset (Fin m)) : ℕ := by
  classical
  exact ((Finset.Icc 1 (z i)).filter fun j =>
    (B.witnesses z i j ∩ P).Nonempty).sup id

noncomputable def Certificate.upper (B : Certificate m) (z : Fin m → ℕ)
    (i : Fin m) (P : Finset (Fin m)) : ℕ := by
  classical
  let cuts := (Finset.range (B.d i)).filter fun j =>
    z i < j ∧ (B.witnesses z i j ∩ P).Nonempty
  exact (insert (B.d i) cuts).min' (by simp)

/-- Real subtraction avoids silently truncating an invalid interval. -/
noncomputable def Certificate.length (B : Certificate m) (z : Fin m → ℕ)
    (i : Fin m) (P : Finset (Fin m)) : ℝ :=
  (B.upper z i P : ℝ) - (B.lower z i P : ℝ)

end SwitchingStable.Universal.Supplement


