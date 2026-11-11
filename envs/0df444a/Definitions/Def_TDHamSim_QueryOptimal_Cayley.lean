-- Prove2me | Definitions.Def_TDHamSim_QueryOptimal_Cayley
-- name    : TDHamSim_QueryOptimal_Cayley
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:17:23.643469+00:00
-- url     : https://prove2.me/theorems/1d48928c-97e1-4f23-a26a-d6daca22d266
-- title:
--   Cayley steps, local transducer and catalyst
-- statement:
--   For $w=\alpha T/J$, the Cayley step and its time-ordered product are
--
--   $$U_j^C=(I-iwH(t_j)/(2\alpha))(I+iwH(t_j)/(2\alpha))^{-1},\qquad U_C=U_{J-1}^C\cdots U_0^C.$$
--
--   The midpoint, local catalyst, zero-ancilla embedding, constants $c,s$, local operator $R$, individual updates $R_j$, their product $S^\circ$, and transducer $S=S^\circ(I\oplus\mathrm{HAM\!\text{-}\!T})$ are computed from these data. The map $\Gamma$ collects the local catalysts by time label. The private and cross blocks, the lower-triangular operator $\Delta$, and the polynomials $G_N$ and $Q$ are defined directly. These operators are shared by all milestones; none is supplied through an assumed identity.
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Definition 1, p.7; (10)–(29), pp.12–17; (41)–(47), pp.20–21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Model

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

noncomputable def cayley {n : ℕ} (α w : ℝ) (K : Mat (Bits n)) : Mat (Bits n) :=
  (1 - (Complex.I * (w / (2 * α) : ℝ)) • K) *
    (1 + (Complex.I * (w / (2 * α) : ℝ)) • K)⁻¹
noncomputable def cayleyPrefix {n : ℕ} (H : ℝ → Mat (Bits n)) (α T : ℝ) (J k : ℕ) :
    Mat (Bits n) :=
  ((List.range k).map fun j => cayley α (stepWeight α T J) (H (grid J T j))).foldl
    (fun acc U => U * acc) 1
noncomputable def cayleyProduct {n : ℕ} (H : ℝ → Mat (Bits n)) (α T : ℝ) (J : ℕ) :=
  cayleyPrefix H α T J J
noncomputable def midpoint {n : ℕ} (α w : ℝ) (K : Mat (Bits n)) : Mat (Bits n) :=
  (1 + (Complex.I * (w / (2 * α) : ℝ)) • K)⁻¹
noncomputable def cosine (w : ℝ) : ℝ := (1 - w / 2) / (1 + w / 2)
noncomputable def sine (w : ℝ) : ℝ := Real.sqrt (2 * w) / (1 + w / 2)
noncomputable def iota (a n : ℕ) : Matrix (Bits a × Bits n) (Bits n) ℂ :=
  fun x y => if x.1 = (fun _ => false) ∧ x.2 = y then 1 else 0
noncomputable def ancProj (a n : ℕ) : Mat (Bits a × Bits n) :=
  iota a n * (iota a n).conjTranspose
noncomputable def catalyst {n a : ℕ} (α w : ℝ) (K : Mat (Bits n))
    (O : Mat (Bits a × Bits n)) : Matrix (Bits a × Bits n) (Bits n) ℂ :=
  (Real.sqrt (w / 2) : ℂ) • ((1 + Complex.I • O) * iota a n * midpoint α w K)

noncomputable def localR (a n : ℕ) (w : ℝ) : Mat (Sum (Bits n) (Bits a × Bits n)) :=
  Matrix.fromBlocks ((cosine w : ℂ) • 1)
    ((-Complex.I * sine w) • (iota a n).conjTranspose)
    ((sine w : ℂ) • iota a n)
    (Complex.I • ((cosine w : ℂ) • ancProj a n + 1 - ancProj a n))

abbrev Priv (J a n : ℕ) := Fin J × (Bits a × Bits n)
abbrev Space (J a n : ℕ) := Sum (Bits n) (Priv J a n)

noncomputable def join {ι κ : Type} (v : Ket ι) (w : Ket κ) : Ket (Sum ι κ) :=
  WithLp.toLp 2 (Sum.elim v w)

noncomputable def update (J a n : ℕ) (w : ℝ) (j : Fin J) : Mat (Space J a n)
  | Sum.inl x, Sum.inl y => if x = y then cosine w else 0
  | Sum.inl x, Sum.inr y =>
      if y.1 = j then -Complex.I * sine w * (iota a n).conjTranspose x y.2 else 0
  | Sum.inr x, Sum.inl y => if x.1 = j then sine w * iota a n x.2 y else 0
  | Sum.inr x, Sum.inr y =>
      if x.1 = y.1 then
        if x.1 = j then
          (Complex.I • ((cosine w : ℂ) • ancProj a n + 1 - ancProj a n)) x.2 y.2
        else (1 : Mat (Bits a × Bits n)) x.2 y.2
      else 0

noncomputable def updates (J a n : ℕ) (w : ℝ) : Mat (Space J a n) :=
  (List.ofFn (update J a n w)).foldl (fun acc R => R * acc) 1
noncomputable def querySum {J a n : ℕ} (O : Fin J → Mat (Bits a × Bits n)) : Mat (Space J a n) :=
  Matrix.fromBlocks 1 0 0 (hamT O)
noncomputable def transducer {J a n : ℕ} (w : ℝ) (O : Fin J → Mat (Bits a × Bits n)) :=
  updates J a n w * querySum O
noncomputable def gamma {J a n : ℕ} (H : ℝ → Mat (Bits n)) (α T : ℝ)
    (O : Fin J → Mat (Bits a × Bits n)) : Matrix (Priv J a n) (Bits n) ℂ :=
  fun x y => (catalyst α (stepWeight α T J) (H (grid J T x.1)) (O x.1) *
    cayleyPrefix H α T J x.1) x.2 y
noncomputable def privateBlock {J a n : ℕ} (w : ℝ) (O : Fin J → Mat (Bits a × Bits n)) :
    Mat (Priv J a n) := fun x y => transducer w O (Sum.inr x) (Sum.inr y)
noncomputable def crossBlock {J a n : ℕ} (w : ℝ) (O : Fin J → Mat (Bits a × Bits n)) :
    Matrix (Bits n) (Priv J a n) ℂ := fun x y => transducer w O (Sum.inl x) (Sum.inr y)
noncomputable def delta (J a n : ℕ) (w : ℝ) : Mat (Priv J a n) :=
  fun x y =>
    if x.1 = y.1 then (1 - cosine w) * ancProj a n x.2 y.2
    else if y.1 < x.1 then (sine w ^ 2 * cosine w ^ (x.1.val - y.1.val - 1)) * ancProj a n x.2 y.2
    else 0
noncomputable def Q {ι : Type} [Fintype ι] [DecidableEq ι] (A : Mat ι) : Mat ι :=
  (1 / 2 : ℂ) • (1 + A ^ 2)
noncomputable def G {ι : Type} [Fintype ι] [DecidableEq ι] (N : ℕ) (A : Mat ι) : Mat ι :=
  (N : ℂ)⁻¹ • ∑ k ∈ Finset.range N, A ^ k

/-- Definition 1, p.7. This is a predicate on actual operators, with no resource fields. -/
def IsTransducer {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Mat (Sum ι κ)) (U : Mat ι) : Prop :=
  IsUnitary S ∧ IsUnitary U ∧ ∃ Γ : Matrix κ ι ℂ,
    ∀ v : Ket ι, act S (join v (act Γ v)) = join (act U v) (act Γ v)

end TDHamSim.QueryOptimal


