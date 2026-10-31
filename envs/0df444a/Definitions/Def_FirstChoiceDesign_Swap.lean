-- Prove2me | Definitions.Def_FirstChoiceDesign_Swap
-- name    : FirstChoiceDesign_Swap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:38.82842+00:00
-- url     : https://prove2.me/theorems/4cf38c11-1671-420f-bd11-5e0e9fb9aa92
-- title:
--   Column replacement and the switches $\delta_s(r)$, $\sigma^*(r)$, $\hat\sigma(r)$
-- statement:
--   For a column $c$ and a matrix $M$ indexed by students and schools, $(c,M_{-s})$ is $M$ with column $s$ replaced by $c$. This is the notation $(\delta_s(r),r_{-s})$ of Lemma 3 and $((\rho'_s,r'_s),(\rho^*_{-s},r^*_{-s}))$ of Definition 3.
--
--   The switch of students $a$ and $b$ exchanges their lottery numbers: at school $s$ only (`swapAt`, the permutation $\delta_s(r)$), or at every school (`swapAll`). The **regime-respecting switch** `swapReg` is `swapAt` under MTB and `swapAll` under STB. With the pivot students it is $\sigma^*(r)$, and with two consecutive students it is $\hat\sigma(r)$.
--
--   **Formalization Note** "Let $\hat\sigma(r)=\times_{|S|}\hat\sigma_s(r)$" is read like $\sigma^*$, as the same switch at every school. On STB-consistent $r$ this agrees with copying column $s$ to all schools.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 3 p.41, σ* and σ̂ p.46, Definition 3 p.14

import Definitions.Def_FirstChoiceDesign_Lottery

namespace FirstChoiceDesign

/-- The profile `(c, M_{-s})`: column `s` of `M` replaced by `c`, all other columns kept. It is the
notation `(δ_s(r), r_{-s})` of Lemma 3, p.41, and `((ρ'_s, r'_s), (ρ*_{-s}, r*_{-s}))` of Definition
3, p.14. Columns are schools, for priorities and lottery numbers alike. -/
def updateColumn {n m : ℕ} {α : Type*} (s : Fin m) (c : Fin n → α) (M : Fin n → Fin m → α) :
    Fin n → Fin m → α :=
  fun i t => if t = s then c i else M i t

/-- `(δ_s(r), r_{-s})` where `δ_s(r)` switches only students `a` and `b` in `r_s`, Lemma 3, p.41. -/
def swapAt {n m : ℕ} (s : Fin m) (a b : Fin n) (r : Lottery n m) : Lottery n m :=
  updateColumn s (fun i => r (Equiv.swap a b i) s) r

/-- The switch of `a` and `b` in every column `r_s'`, `s' ∈ S`, including `s`: the STB case of `σ*`,
p.46. -/
def swapAll {n m : ℕ} (a b : Fin n) (r : Lottery n m) : Lottery n m :=
  fun i t => r (Equiv.swap a b i) t

/-- The regime-respecting switch of `a` and `b` that defines `σ*(r)` and `σ̂(r)`, p.46: only in `r_s`
under MTB, in every `r_s'` under STB.

**Formalization Note** "Let `σ̂(r) = ×_{|S|} σ̂_s(r)`" (p.46) is read as for `σ*`, as the same switch at
every school. It agrees with copying column `s` to every school on STB-consistent `r`. -/
def swapReg {n m : ℕ} : Regime → Fin m → Fin n → Fin n → Lottery n m → Lottery n m
  | .MTB, s, a, b, r => swapAt s a b r
  | .STB, _, a, b, r => swapAll a b r

end FirstChoiceDesign


