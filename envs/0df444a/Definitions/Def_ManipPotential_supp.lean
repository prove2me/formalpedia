-- Prove2me | Definitions.Def_ManipPotential_supp
-- name    : ManipPotential_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:38.038954+00:00
-- url     : https://prove2.me/theorems/61103191-32da-4817-a486-3cf4bf9c397d
-- title:
--   Support $\mathrm{supp}(x) = \{j : x_j > 0\}$
-- statement:
--   For a nonnegative coefficient vector $x \in \mathbb R^m_{\ge 0}$ (or $\mathbb Q^m_{\ge 0}$), its **support** is $\mathrm{supp}(x) = \{ j \in [m] : x_j > 0 \}$. The statement "$g(\cdot) \in \{c_j : j \in S\}$" for $S = \mathrm{supp}(x)$ reads "the winner's index lies in the support".
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.3, p.27, and Table 2, p.38

import Mathlib

namespace ManipPotential

/-- The support `supp(x) = {j : x_j > 0}` of a nonnegative coefficient vector (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6,
Lemma 6.3, p.27, and Table 2, p.38). -/
def supp {m : ℕ} {R : Type*} [Preorder R] [Zero R] [DecidableLT R] (x : Fin m → R) :
    Finset (Fin m) :=
  Finset.univ.filter (fun j => 0 < x j)

end ManipPotential


