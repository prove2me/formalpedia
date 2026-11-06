-- Prove2me | Definitions.Def_Monodromy_Counter
-- name    : Monodromy_Counter
-- status  : Definition
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:20:57.14806+00:00
-- url     : https://prove2.me/theorems/5b3cc91e-7529-4032-ad54-d2b0dc238ad4
-- title:
--   Finite Counter Machines, Reversible Recording and Prime Compression
-- statement:
--   Defines finite natural-counter machines and finite integer-counter edge tables with their optional-step and partial-evaluation semantics. Contains native two-counter compilation, finite Turing-table arithmetic, prime coding, reversible routing and radix networks, history recording with workspace restoration, and compression of reversible multi-register graphs into two registers with marked first-return semantics.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Instruction at L29-L32 [UTF-8 948:1072].
--   Monodromy.Counter.Configuration at L34-L36 [UTF-8 1074:1155].
--   Monodromy.Counter.Program at L38-L38 [UTF-8 1157:1212].
--   Monodromy.Counter.step at L40-L49 [UTF-8 1214:1666].
--   Monodromy.Counter.eval at L75-L77 [UTF-8 2679:2890].
--   Monodromy.Counter.tick at L79-L81 [UTF-8 2892:3088].
--   Monodromy.Counter.mapInstruction at L87-L91 [UTF-8 3112:3422].
--   Monodromy.Counter.mapConfiguration at L93-L94 [UTF-8 3424:3566].
--   Monodromy.CounterContinuation.label at L144-L146 [UTF-8 5502:5687].
--   Monodromy.CounterContinuation.memoryGate at L152-L152 [UTF-8 5864:5946].
--   Monodromy.CounterContinuation.zeroGate at L154-L154 [UTF-8 5948:6036].
--   Monodromy.CounterContinuation.instructionWord at L156-L168 [UTF-8 6038:6683].
--   Monodromy.CounterContinuation.instructionStop at L170-L171 [UTF-8 6685:6818].
--   Monodromy.CounterContinuation.stopping at L173-L174 [UTF-8 6820:6985].
--   Monodromy.CounterContinuation.wordTable at L176-L178 [UTF-8 6987:7164].
--   Monodromy.CounterContinuation.stopTable at L180-L182 [UTF-8 7166:7336].
--   Monodromy.CounterContinuation.compile at L184-L185 [UTF-8 7338:7477].
--   Monodromy.CounterContinuation.encode at L187-L188 [UTF-8 7479:7626].
--   Monodromy.CounterContinuation.SourceBoundary at L506-L507 [UTF-8 23026:23174].
--   Monodromy.PrimeCode.Basis at L596-L600 [UTF-8 27317:27537].
--   Monodromy.PrimeCode.Basis.encode at L606-L606 [UTF-8 27594:27688].
--   Monodromy.PrimeCode.Basis.decode at L608-L608 [UTF-8 27690:27784].
--   Monodromy.PrimeCode.prime at L687-L688 [UTF-8 31205:31386].
--   Monodromy.PrimeCode.encode at L690-L691 [UTF-8 31388:31489].
--   Monodromy.PrimeCode.prime_prime at L693-L694 [UTF-8 31491:31604].
--   Monodromy.PrimeCode.decode at L696-L696 [UTF-8 31606:31694].
--   Monodromy.PrimeCode.three at L698-L704 [UTF-8 31696:31956].
--   Monodromy.Counter.RegisterRelocation.instruction at L762-L765 [UTF-8 34816:35041].
--   Monodromy.Counter.RegisterRelocation.program at L767-L768 [UTF-8 35043:35178].
--   Monodromy.Counter.RegisterRelocation.embed at L770-L773 [UTF-8 35180:35454].
--   Monodromy.Counter.RegisterRelocation.pairIntoThree at L829-L831 [UTF-8 38517:38717].
--   Monodromy.CounterMultiplication.phase at L883-L885 [UTF-8 40954:41150].
--   Monodromy.CounterMultiplication.transfer at L887-L887 [UTF-8 41152:41228].
--   Monodromy.CounterMultiplication.restore at L888-L888 [UTF-8 41229:41304].
--   Monodromy.CounterMultiplication.finish at L889-L889 [UTF-8 41305:41379].
--   Monodromy.CounterMultiplication.program at L891-L896 [UTF-8 41381:41773].
--   Monodromy.CounterMultiplication.configuration at L898-L899 [UTF-8 41775:41937].
--   Monodromy.Counter.DivMod.size at L1059-L1060 [UTF-8 49479:49579].
--   Monodromy.Counter.DivMod.consume at L1062-L1062 [UTF-8 49581:49674].
--   Monodromy.Counter.DivMod.transfer at L1063-L1063 [UTF-8 49675:49773].
--   Monodromy.Counter.DivMod.restore at L1064-L1064 [UTF-8 49774:49875].
--   Monodromy.Counter.DivMod.finish at L1065-L1065 [UTF-8 49876:49976].
--   Monodromy.Counter.DivMod.bump at L1066-L1066 [UTF-8 49977:50039].
--   Monodromy.Counter.DivMod.next at L1068-L1069 [UTF-8 50041:50180].
--   Monodromy.Counter.DivMod.program at L1071-L1080 [UTF-8 50182:50741].
--   Monodromy.Counter.DivMod.configuration at L1112-L1114 [UTF-8 52226:52440].
--   Monodromy.Counter.DivMod.residue at L1160-L1161 [UTF-8 54600:54703].
--   Monodromy.CounterPrimeProbe.size at L1268-L1269 [UTF-8 59905:60037].
--   Monodromy.CounterPrimeProbe.divBlock at L1271-L1272 [UTF-8 60039:60139].
--   Monodromy.CounterPrimeProbe.mulAddress at L1274-L1275 [UTF-8 60141:60242].
--   Monodromy.CounterPrimeProbe.divAddress at L1277-L1283 [UTF-8 60244:60616].
--   Monodromy.CounterPrimeProbe.entry at L1285-L1285 [UTF-8 60618:60687].
--   Monodromy.CounterPrimeProbe.success at L1286-L1286 [UTF-8 60688:60756].
--   Monodromy.CounterPrimeProbe.failure at L1287-L1287 [UTF-8 60757:60832].
--   Monodromy.CounterPrimeProbe.program at L1289-L1293 [UTF-8 60834:61189].
--   Monodromy.CounterPrimeProbe.configuration at L1295-L1296 [UTF-8 61191:61326].
--   Monodromy.Counter.TuringCompiler.base at L1488-L1488 [UTF-8 70390:70413].
--   Monodromy.Counter.TuringCompiler.base_neZero at L1489-L1489 [UTF-8 70414:70476].
--   Monodromy.Counter.TuringCompiler.Row at L1491-L1491 [UTF-8 70478:70506].
--   Monodromy.Counter.TuringCompiler.Phase at L1492-L1492 [UTF-8 70507:70593].
--   Monodromy.Counter.TuringCompiler.Address at L1493-L1493 [UTF-8 70594:70630].
--   Monodromy.Counter.TuringCompiler.size at L1495-L1495 [UTF-8 70632:70676].
--   Monodromy.Counter.TuringCompiler.address at L1497-L1497 [UTF-8 70678:70744].
--   Monodromy.Counter.TuringCompiler.dispatch at L1499-L1499 [UTF-8 70746:70824].
--   Monodromy.Counter.TuringCompiler.multiply at L1500-L1501 [UTF-8 70825:70943].
--   Monodromy.Counter.TuringCompiler.add at L1502-L1503 [UTF-8 70944:71066].
--   Monodromy.Counter.TuringCompiler.divide at L1504-L1505 [UTF-8 71067:71203].
--   Monodromy.Counter.TuringCompiler.address_dispatch at L1507-L1510 [UTF-8 71205:71385].
--   Monodromy.Counter.TuringCompiler.counters at L1531-L1531 [UTF-8 72274:72342].
--   Monodromy.Counter.TuringCompiler.encode at L1533-L1535 [UTF-8 72344:72551].
--   Monodromy.Counter.TuringCompiler.pushRegister at L1563-L1563 [UTF-8 73471:73530].
--   Monodromy.Counter.TuringCompiler.popRegister at L1564-L1564 [UTF-8 73531:73589].
--   Monodromy.Counter.TuringCompiler.mulTarget at L1566-L1568 [UTF-8 73591:73768].
--   Monodromy.Counter.TuringCompiler.symbol at L1570-L1571 [UTF-8 73770:73888].
--   Monodromy.Counter.TuringCompiler.divTarget at L1573-L1577 [UTF-8 73890:74151].
--   Monodromy.Counter.TuringCompiler.previous at L1595-L1596 [UTF-8 74861:74978].
--   Monodromy.Counter.TuringCompiler.body at L1598-L1624 [UTF-8 74980:76285].
--   Monodromy.Counter.TuringCompiler.program at L1626-L1627 [UTF-8 76287:76421].
--   Monodromy.Counter.TuringCompiler.program_dispatch at L1629-L1636 [UTF-8 76423:76867].
--   Monodromy.Counter.TuringCompiler.Boundary at L1655-L1656 [UTF-8 77696:77858].
--   Monodromy.Counter.TuringCompiler.InternalStep at L1683-L1686 [UTF-8 78848:79115].
--   Monodromy.Counter.TuringCompiler.InternalReaches at L1688-L1689 [UTF-8 79117:79233].
--   Monodromy.Counter.TuringCompiler.frame at L1752-L1753 [UTF-8 82337:82482].
--   Monodromy.Counter.TuringCompiler.FirstReturn at L1919-L1923 [UTF-8 91846:92149].
--   Monodromy.Counter.Compression.prime_neZero at L1999-L2000 [UTF-8 95698:95826].
--   Monodromy.Counter.Compression.blockSize at L2002-L2005 [UTF-8 95828:96009].
--   Monodromy.Counter.Compression.Address at L2007-L2007 [UTF-8 96011:96105].
--   Monodromy.Counter.Compression.size at L2009-L2009 [UTF-8 96107:96177].
--   Monodromy.Counter.Compression.address at L2010-L2010 [UTF-8 96178:96273].
--   Monodromy.Counter.Compression.dispatch at L2012-L2013 [UTF-8 96275:96383].
--   Monodromy.Counter.Compression.multiply at L2015-L2018 [UTF-8 96385:96665].
--   Monodromy.Counter.Compression.probe at L2020-L2023 [UTF-8 96667:96981].
--   Monodromy.Counter.Compression.mulTarget at L2047-L2051 [UTF-8 98166:98519].
--   Monodromy.Counter.Compression.probeTarget at L2053-L2058 [UTF-8 98521:99014].
--   Monodromy.Counter.Compression.body at L2078-L2100 [UTF-8 100117:101312].
--   Monodromy.Counter.Compression.program at L2102-L2103 [UTF-8 101314:101432].
--   Monodromy.Counter.Compression.encode at L2153-L2154 [UTF-8 103620:103788].
--   Monodromy.Counter.Compression.Boundary at L2166-L2167 [UTF-8 104221:104331].
--   Monodromy.Counter.Compression.InternalStep at L2189-L2192 [UTF-8 105293:105560].
--   Monodromy.Counter.Compression.InternalReaches at L2194-L2195 [UTF-8 105562:105656].
--   Monodromy.Counter.Compression.FirstReturn at L2341-L2343 [UTF-8 113879:114158].
--   Monodromy.Counter.EntryDispatch.program at L2463-L2467 [UTF-8 120749:121088].
--   Monodromy.Counter.EntryDispatch.entryState at L2469-L2470 [UTF-8 121090:121218].
--   Monodromy.Counter.Reversible.Action at L2540-L2543 [UTF-8 124446:124573].
--   Monodromy.Counter.Reversible.State at L2545-L2545 [UTF-8 124575:124627].
--   Monodromy.Counter.Reversible.Edge at L2547-L2551 [UTF-8 124629:124738].
--   Monodromy.Counter.Reversible.Table at L2553-L2553 [UTF-8 124740:124788].
--   Monodromy.Counter.Reversible.Action.enabled at L2559-L2561 [UTF-8 124828:124972].
--   Monodromy.Counter.Reversible.Action.instDecidableEnabled at L2563-L2564 [UTF-8 124974:125127].
--   Monodromy.Counter.Reversible.Action.apply at L2566-L2568 [UTF-8 125129:125303].
--   Monodromy.Counter.Reversible.Action.UnitShift at L2570-L2573 [UTF-8 125305:125490].
--   Monodromy.Counter.Reversible.Action.Compatible at L2575-L2578 [UTF-8 125492:125724].
--   Monodromy.Counter.Reversible.Edge.enabled at L2623-L2624 [UTF-8 127555:127670].
--   Monodromy.Counter.Reversible.Edge.instDecidableEnabled at L2626-L2627 [UTF-8 127672:127840].
--   Monodromy.Counter.Reversible.Edge.execute at L2629-L2630 [UTF-8 127842:127949].
--   Monodromy.Counter.Reversible.Deterministic at L2634-L2637 [UTF-8 127961:128231].
--   Monodromy.Counter.Reversible.TargetCompatible at L2639-L2642 [UTF-8 128233:128520].
--   Monodromy.Counter.Reversible.Complete at L2644-L2647 [UTF-8 128522:128754].
--   Monodromy.Counter.Reversible.StepRel at L2649-L2651 [UTF-8 128756:128978].
--   Monodromy.Counter.Reversible.step at L2687-L2691 [UTF-8 130953:131283].
--   Monodromy.Counter.Reversible.Action.IsShift at L2730-L2732 [UTF-8 132896:132973].
--   Monodromy.Counter.Reversible.Action.instDecidableIsShift at L2734-L2735 [UTF-8 132975:133094].
--   Monodromy.Counter.Reversible.Action.instDecidableCompatible at L2737-L2738 [UTF-8 133096:133251].
--   Monodromy.Counter.Reversible.Action.Compatible.one_enabled at L2740-L2751 [UTF-8 133253:133813].
--   Monodromy.Counter.Reversible.Action.test_disabled at L2753-L2757 [UTF-8 133815:134062].
--   Monodromy.Counter.Reversible.CoveredAt at L2761-L2766 [UTF-8 134076:134521].
--   Monodromy.Counter.Reversible.instDecidableCoveredAt at L2768-L2773 [UTF-8 134523:134951].
--   Monodromy.Counter.Reversible.complete_of_covered at L2775-L2786 [UTF-8 134953:135575].
--   Monodromy.Counter.Reversible.covered_of_complete at L2788-L2806 [UTF-8 135577:136574].
--   Monodromy.Counter.Reversible.complete_iff_covered at L2808-L2811 [UTF-8 136576:136889].
--   Monodromy.Counter.Reversible.decideComplete at L2813-L2817 [UTF-8 136891:137204].
--   Monodromy.Counter.Reversible.eval at L2819-L2821 [UTF-8 137206:137389].
--   Monodromy.Counter.Reversible.CompleteOn at L2823-L2826 [UTF-8 137391:137675].
--   Monodromy.Counter.Reversible.Stable at L2828-L2830 [UTF-8 137677:137909].
--   Monodromy.Counter.Reversible.reverseAction at L2846-L2848 [UTF-8 138564:138712].
--   Monodromy.Counter.Reversible.reverseAction_compatible at L2873-L2876 [UTF-8 139682:139903].
--   Monodromy.Counter.Reversible.reverseEdge at L2890-L2891 [UTF-8 140208:140315].
--   Monodromy.Counter.Reversible.reverseTable at L2898-L2899 [UTF-8 140459:140555].
--   Monodromy.Counter.Reversible.reverseTable_deterministic at L2906-L2909 [UTF-8 140722:140983].
--   Monodromy.Counter.Reversible.reverseTable_targetCompatible at L2911-L2914 [UTF-8 140985:141255].
--   Monodromy.ReversiblePorts.mate at L2959-L2963 [UTF-8 143189:143532].
--   Monodromy.ReversiblePorts.Matching at L2965-L2967 [UTF-8 143534:143727].
--   Monodromy.ReversiblePorts.mate_some at L2969-L2986 [UTF-8 143729:144433].
--   Monodromy.ReversiblePorts.exchange at L2988-L2990 [UTF-8 144435:144680].
--   Monodromy.ReversiblePorts.exchange_involutive at L2992-L3007 [UTF-8 144682:145426].
--   Monodromy.ReversiblePorts.pairing at L3009-L3014 [UTF-8 145428:145747].
--   Monodromy.ReversiblePorts.permutation at L3016-L3018 [UTF-8 145749:145968].
--   Monodromy.ReversiblePorts.permutation_apply at L3020-L3023 [UTF-8 145970:146233].
--   Monodromy.ReversiblePorts.permutation_involutive at L3025-L3030 [UTF-8 146235:146610].
--   Monodromy.ReversiblePorts.actionGuard at L3055-L3058 [UTF-8 147907:148105].
--   Monodromy.ReversiblePorts.compatible_guards_ne at L3060-L3064 [UTF-8 148107:148472].
--   Monodromy.ReversiblePorts.selected at L3077-L3079 [UTF-8 149020:149231].
--   Monodromy.ReversiblePorts.selected_iff at L3081-L3083 [UTF-8 149233:149439].
--   Monodromy.ReversiblePorts.sourceMatching at L3085-L3091 [UTF-8 149441:149880].
--   Monodromy.ReversiblePorts.targetMatching at L3093-L3099 [UTF-8 149882:150318].
--   Monodromy.ReversiblePorts.guards at L3101-L3103 [UTF-8 150320:150522].
--   Monodromy.ReversibleRouting.CompatibleOwner at L3126-L3129 [UTF-8 151037:151333].
--   Monodromy.ReversibleRouting.route at L3134-L3136 [UTF-8 151457:151701].
--   Monodromy.ReversibleRouting.run at L3138-L3140 [UTF-8 151703:151946].
--   Monodromy.ReversibleRouting.run_nil at L3142-L3142 [UTF-8 151948:152039].
--   Monodromy.ReversibleRouting.point at L3149-L3151 [UTF-8 152315:152538].
--   Monodromy.ReversibleRouting.route_involutive at L3168-L3183 [UTF-8 153352:154182].
--   Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy at L3301-L3301 [UTF-8 160522:160586].
--   Monodromy.ReversibleCompilation.displacement at L3303-L3306 [UTF-8 160588:160815].
--   Monodromy.ReversibleCompilation.point at L3319-L3321 [UTF-8 161375:161574].
--   Monodromy.ReversibleCompilation.sourcePoint at L3323-L3324 [UTF-8 161576:161663].
--   Monodromy.ReversibleCompilation.portPoint at L3326-L3327 [UTF-8 161665:161765].
--   Monodromy.ReversibleCompilation.moves at L3346-L3350 [UTF-8 162613:162869].
--   Monodromy.ReversibleCompilation.update at L3352-L3352 [UTF-8 162871:162963].
--   Monodromy.ReversibleCompilation.sourceLayers at L3371-L3374 [UTF-8 163952:164180].
--   Monodromy.ReversibleCompilation.targetLayers at L3376-L3379 [UTF-8 164182:164415].
--   Monodromy.ReversibleCompilation.layers at L3381-L3384 [UTF-8 164417:164726].
--   Monodromy.ReversibleCompilation.layers_length at L3386-L3389 [UTF-8 164728:164982].
--   Monodromy.ReversibleCompilation.stages at L3420-L3424 [UTF-8 167062:167415].
--   Monodromy.ReversibleCompilation.program at L3436-L3438 [UTF-8 167791:168007].
--   Monodromy.ReversibleCompilation.iota at L3440-L3440 [UTF-8 168009:168103].
--   Monodromy.ReversibleCompilation.backwardStages at L3470-L3474 [UTF-8 169687:170071].
--   Monodromy.ReversibleCompilation.stages_update at L3476-L3478 [UTF-8 170073:170279].
--   Monodromy.ReversibleCompilation.stages_involutive at L3480-L3485 [UTF-8 170281:170653].
--   Monodromy.ReversibleCompilation.backward_left at L3487-L3496 [UTF-8 170655:171244].
--   Monodromy.ReversibleCompilation.backward_right at L3498-L3508 [UTF-8 171246:171920].
--   Monodromy.ReversibleCompilation.reverseProgram at L3510-L3513 [UTF-8 171922:172251].
--   Monodromy.ReversibleCompilation.reverse_after_forward at L3515-L3520 [UTF-8 172253:172638].
--   Monodromy.ReversibleCompilation.forward_after_reverse at L3522-L3527 [UTF-8 172640:173027].
--   Monodromy.ReversibleCompilation.executionEquiv at L3529-L3535 [UTF-8 173029:173513].
--   Monodromy.ReversibleCompilation.haltMark at L3562-L3566 [UTF-8 174554:174852].
--   Monodromy.ReversibleCompilation.haltingProgram at L3579-L3582 [UTF-8 175238:175569].
--   Monodromy.Counter.Reversible.RegisterRelocation.mapAction at L3841-L3843 [UTF-8 190604:190784].
--   Monodromy.Counter.Reversible.RegisterRelocation.mapTable at L3849-L3850 [UTF-8 190980:191165].
--   Monodromy.Counter.Reversible.RegisterRelocation.compatible_iff at L3852-L3856 [UTF-8 191167:191503].
--   Monodromy.Counter.Reversible.RegisterRelocation.deterministic at L3858-L3862 [UTF-8 191505:191830].
--   Monodromy.Counter.Reversible.RegisterRelocation.targetCompatible at L3864-L3868 [UTF-8 191832:192166].
--   Monodromy.Counter.Reversible.RegisterRelocation.embed at L3896-L3898 [UTF-8 193431:193676].
--   Monodromy.Counter.Reversible.Glue.leftControl at L3997-L3998 [UTF-8 198768:198932].
--   Monodromy.Counter.Reversible.Glue.rightControl at L4000-L4000 [UTF-8 198934:199020].
--   Monodromy.Counter.Reversible.Glue.mapEdge at L4053-L4054 [UTF-8 201401:201546].
--   Monodromy.Counter.Reversible.Glue.mapState at L4056-L4057 [UTF-8 201548:201664].
--   Monodromy.Counter.Reversible.Glue.table at L4059-L4063 [UTF-8 201666:201997].
--   Monodromy.Counter.Reversible.PortNetwork.Wiring at L4272-L4280 [UTF-8 213105:213666].
--   Monodromy.Counter.Reversible.PortNetwork.Node at L4284-L4285 [UTF-8 213730:213873].
--   Monodromy.Counter.Reversible.PortNetwork.representative at L4287-L4290 [UTF-8 213875:214067].
--   Monodromy.Counter.Reversible.PortNetwork.size at L4292-L4292 [UTF-8 214069:214113].
--   Monodromy.Counter.Reversible.PortNetwork.nodeEquiv at L4294-L4294 [UTF-8 214115:214186].
--   Monodromy.Counter.Reversible.PortNetwork.control at L4296-L4297 [UTF-8 214188:214293].
--   Monodromy.Counter.Reversible.PortNetwork.table at L4299-L4300 [UTF-8 214295:214395].
--   Monodromy.Counter.Reversible.PortNetwork.representative_unlinked at L4311-L4315 [UTF-8 214766:214974].
--   Monodromy.Counter.Reversible.PortNetwork.representative_linked at L4317-L4321 [UTF-8 214976:215177].
--   Monodromy.Counter.Reversible.PortNetwork.control_unlinked_injective at L4338-L4344 [UTF-8 215892:216367].
--   Monodromy.Counter.Reversible.PortNetwork.source_eq_iff at L4346-L4352 [UTF-8 216369:216796].
--   Monodromy.Counter.Reversible.PortNetwork.target_eq_iff at L4354-L4383 [UTF-8 216798:218425].
--   Monodromy.Counter.Reversible.PortNetwork.deterministic at L4385-L4388 [UTF-8 218427:218713].
--   Monodromy.Counter.Reversible.PortNetwork.targetCompatible at L4390-L4393 [UTF-8 218715:219011].
--   Monodromy.Counter.Reversible.PortNetwork.relationLink at L4419-L4424 [UTF-8 220525:220839].
--   Monodromy.Counter.Reversible.PortNetwork.relationLink_some_iff at L4426-L4443 [UTF-8 220841:221537].
--   Monodromy.Counter.Reversible.PortNetwork.relationLink_none_iff at L4445-L4455 [UTF-8 221539:222017].
--   Monodromy.Counter.Reversible.PortNetwork.Wiring.ofRelation at L4457-L4476 [UTF-8 222019:223313].
--   Monodromy.Counter.Reversible.Radix.size at L4491-L4491 [UTF-8 223505:223532].
--   Monodromy.Counter.Reversible.Radix.edges at L4492-L4492 [UTF-8 223533:223561].
--   Monodromy.Counter.Reversible.Radix.Node at L4494-L4494 [UTF-8 223563:223604].
--   Monodromy.Counter.Reversible.Radix.Arc at L4495-L4495 [UTF-8 223605:223645].
--   Monodromy.Counter.Reversible.Radix.nodeEquiv at L4497-L4498 [UTF-8 223647:223760].
--   Monodromy.Counter.Reversible.Radix.arcEquiv at L4500-L4501 [UTF-8 223762:223874].
--   Monodromy.Counter.Reversible.Radix.global at L4503-L4503 [UTF-8 223876:223951].
--   Monodromy.Counter.Reversible.Radix.block at L4504-L4505 [UTF-8 223952:224055].
--   Monodromy.Counter.Reversible.Radix.entry at L4507-L4507 [UTF-8 224057:224095].
--   Monodromy.Counter.Reversible.Radix.finish at L4508-L4508 [UTF-8 224096:224164].
--   Monodromy.Counter.Reversible.Radix.next at L4510-L4513 [UTF-8 224166:224381].
--   Monodromy.Counter.Reversible.Radix.next_eq_block at L4515-L4531 [UTF-8 224383:224990].
--   Monodromy.Counter.Reversible.Radix.next_eq_global at L4533-L4545 [UTF-8 224992:225442].
--   Monodromy.Counter.Reversible.Radix.next_injective at L4547-L4559 [UTF-8 225444:225837].
--   Monodromy.Counter.Reversible.Radix.next_eq_next at L4561-L4563 [UTF-8 225839:225990].
--   Monodromy.Counter.Reversible.Radix.origin at L4565-L4571 [UTF-8 225992:226411].
--   Monodromy.Counter.Reversible.Radix.destination at L4573-L4578 [UTF-8 226413:226791].
--   Monodromy.Counter.Reversible.Radix.operation at L4580-L4585 [UTF-8 226793:227152].
--   Monodromy.Counter.Reversible.Radix.table at L4587-L4589 [UTF-8 227154:227330].
--   Monodromy.Counter.Reversible.Radix.table_arc at L4591-L4594 [UTF-8 227332:227514].
--   Monodromy.Counter.Reversible.Radix.deterministic at L4604-L4616 [UTF-8 227900:228626].
--   Monodromy.Counter.Reversible.Radix.targetCompatible at L4618-L4634 [UTF-8 228628:229443].
--   Monodromy.Counter.Reversible.Radix.point at L4636-L4637 [UTF-8 229445:229550].
--   Monodromy.Counter.Reversible.Radix.instNeZeroNatSize at L4640-L4640 [UTF-8 229553:229603].
--   Monodromy.Counter.Reversible.Radix.admissible at L4642-L4646 [UTF-8 229605:229935].
--   Monodromy.Counter.Reversible.Radix.Valid at L4648-L4650 [UTF-8 229937:230095].
--   Monodromy.Counter.Reversible.Radix.origin_ne_finish at L4695-L4700 [UTF-8 232338:232583].
--   Monodromy.Counter.Reversible.Radix.no_outgoing_finish at L4702-L4709 [UTF-8 232585:232990].
--   Monodromy.Counter.Reversible.Radix.no_incoming_entry at L4933-L4940 [UTF-8 246562:247062].
--   Monodromy.Counter.Reversible.RadixObservation.RawNode at L4984-L4984 [UTF-8 249013:249069].
--   Monodromy.Counter.Reversible.RadixObservation.RawArc at L4985-L4985 [UTF-8 249070:249126].
--   Monodromy.Counter.Reversible.RadixObservation.rawSize at L4987-L4987 [UTF-8 249128:249171].
--   Monodromy.Counter.Reversible.RadixObservation.edges at L4988-L4988 [UTF-8 249172:249214].
--   Monodromy.Counter.Reversible.RadixObservation.rawNodeEquiv at L4990-L4991 [UTF-8 249216:249344].
--   Monodromy.Counter.Reversible.RadixObservation.arcEquiv at L4993-L4994 [UTF-8 249346:249467].
--   Monodromy.Counter.Reversible.RadixObservation.rawControl at L4996-L4997 [UTF-8 249469:249622].
--   Monodromy.Counter.Reversible.RadixObservation.component at L4999-L5000 [UTF-8 249624:249773].
--   Monodromy.Counter.Reversible.RadixObservation.component_deterministic at L5002-L5006 [UTF-8 249775:250011].
--   Monodromy.Counter.Reversible.RadixObservation.component_targetCompatible at L5008-L5013 [UTF-8 250013:250262].
--   Monodromy.Counter.Reversible.RadixObservation.rawTable at L5015-L5017 [UTF-8 250264:250443].
--   Monodromy.Counter.Reversible.RadixObservation.rawTable_arc at L5019-L5022 [UTF-8 250445:250712].
--   Monodromy.Counter.Reversible.RadixObservation.rawControl_eq_iff at L5024-L5030 [UTF-8 250714:251118].
--   Monodromy.Counter.Reversible.RadixObservation.raw_deterministic at L5032-L5040 [UTF-8 251120:251651].
--   Monodromy.Counter.Reversible.RadixObservation.raw_targetCompatible at L5042-L5050 [UTF-8 251653:252193].
--   Monodromy.Counter.Reversible.RadixObservation.finishQuery at L5052-L5056 [UTF-8 252195:252474].
--   Monodromy.Counter.Reversible.RadixObservation.finishQuery_some at L5063-L5077 [UTF-8 252669:253338].
--   Monodromy.Counter.Reversible.RadixObservation.finishQuery_source at L5079-L5084 [UTF-8 253340:253666].
--   Monodromy.Counter.Reversible.RadixObservation.link at L5086-L5092 [UTF-8 253668:254066].
--   Monodromy.Counter.Reversible.RadixObservation.link_backward at L5094-L5098 [UTF-8 254068:254309].
--   Monodromy.Counter.Reversible.RadixObservation.link_some at L5107-L5125 [UTF-8 254638:255843].
--   Monodromy.Counter.Reversible.RadixObservation.wiring at L5127-L5166 [UTF-8 255845:258240].
--   Monodromy.Counter.Reversible.RadixObservation.size at L5168-L5168 [UTF-8 258242:258346].
--   Monodromy.Counter.Reversible.RadixObservation.table at L5170-L5171 [UTF-8 258348:258495].
--   Monodromy.Counter.Reversible.RadixObservation.front at L5173-L5175 [UTF-8 258497:258712].
--   Monodromy.Counter.Reversible.RadixObservation.back at L5177-L5179 [UTF-8 258714:258928].
--   Monodromy.Counter.Reversible.RadixObservation.deterministic at L5181-L5182 [UTF-8 258930:259093].
--   Monodromy.Counter.Reversible.RadixObservation.targetCompatible at L5184-L5185 [UTF-8 259095:259270].
--   Monodromy.Counter.Reversible.RadixObservation.inputPort at L5212-L5213 [UTF-8 260520:260670].
--   Monodromy.Counter.Reversible.RadixObservation.outputPort at L5215-L5216 [UTF-8 260672:260822].
--   Monodromy.Counter.Reversible.RadixObservation.point at L5218-L5219 [UTF-8 260824:261004].
--   Monodromy.Counter.Reversible.RadixObservation.instNeZeroNatSize at L5221-L5224 [UTF-8 261006:261336].
--   Monodromy.Counter.Recorded.push at L5312-L5314 [UTF-8 266336:266497].
--   Monodromy.Counter.Recorded.branch at L5335-L5339 [UTF-8 267460:267727].
--   Monodromy.Counter.Recorded.tag at L5341-L5342 [UTF-8 267729:267856].
--   Monodromy.Counter.Recorded.restore at L5344-L5354 [UTF-8 267858:268423].
--   Monodromy.Counter.Recorded.State at L5393-L5393 [UTF-8 270040:270092].
--   Monodromy.Counter.Recorded.step at L5395-L5397 [UTF-8 270094:270355].
--   Monodromy.Counter.Reversible.Recording.base at L5465-L5465 [UTF-8 273389:273426].
--   Monodromy.Counter.Reversible.Recording.base_nonzero at L5467-L5467 [UTF-8 273428:273501].
--   Monodromy.Counter.Reversible.Recording.Node at L5469-L5469 [UTF-8 273503:273574].
--   Monodromy.Counter.Reversible.Recording.size at L5471-L5471 [UTF-8 273576:273631].
--   Monodromy.Counter.Reversible.Recording.nodeEquiv at L5473-L5474 [UTF-8 273633:273756].
--   Monodromy.Counter.Reversible.Recording.copy at L5476-L5477 [UTF-8 273758:273874].
--   Monodromy.Counter.Reversible.Recording.mid at L5479-L5479 [UTF-8 273876:273938].
--   Monodromy.Counter.Reversible.Recording.dispatch at L5481-L5481 [UTF-8 273940:274016].
--   Monodromy.Counter.Reversible.Recording.port at L5483-L5484 [UTF-8 274018:274124].
--   Monodromy.Counter.Reversible.Recording.digit at L5486-L5491 [UTF-8 274126:274393].
--   Monodromy.Counter.Reversible.Recording.digit_eq_iff at L5493-L5504 [UTF-8 274395:274860].
--   Monodromy.Counter.Reversible.Recording.Active at L5506-L5511 [UTF-8 274862:275112].
--   Monodromy.Counter.Reversible.Recording.active_decidable at L5513-L5516 [UTF-8 275114:275297].
--   Monodromy.Counter.Reversible.Recording.Extra at L5518-L5518 [UTF-8 275299:275393].
--   Monodromy.Counter.Reversible.Recording.historyRegister at L5520-L5520 [UTF-8 275395:275464].
--   Monodromy.Counter.Reversible.Recording.historyRegister_injective at L5522-L5527 [UTF-8 275466:275701].
--   Monodromy.Counter.Reversible.Recording.packing at L5529-L5530 [UTF-8 275703:275878].
--   Monodromy.Counter.Reversible.Recording.packing_deterministic at L5532-L5534 [UTF-8 275880:276092].
--   Monodromy.Counter.Reversible.Recording.packing_targetCompatible at L5536-L5538 [UTF-8 276094:276315].
--   Monodromy.Counter.Reversible.Recording.packing_no_outgoing_dispatch at L5540-L5542 [UTF-8 276317:276492].
--   Monodromy.Counter.Reversible.Recording.packing_no_incoming_port at L5544-L5547 [UTF-8 276494:276741].
--   Monodromy.Counter.Reversible.Recording.extraOrigin at L5549-L5554 [UTF-8 276743:277105].
--   Monodromy.Counter.Reversible.Recording.extraDestination at L5556-L5563 [UTF-8 277107:277590].
--   Monodromy.Counter.Reversible.Recording.extraOperation at L5565-L5572 [UTF-8 277592:278049].
--   Monodromy.Counter.Reversible.Recording.extraEdge at L5574-L5576 [UTF-8 278051:278267].
--   Monodromy.Counter.Reversible.Recording.Arc at L5578-L5579 [UTF-8 278269:278372].
--   Monodromy.Counter.Reversible.Recording.edges at L5581-L5582 [UTF-8 278374:278482].
--   Monodromy.Counter.Reversible.Recording.arcEquiv at L5584-L5585 [UTF-8 278484:278660].
--   Monodromy.Counter.Reversible.Recording.arcEdge at L5587-L5589 [UTF-8 278662:278852].
--   Monodromy.Counter.Reversible.Recording.table at L5591-L5592 [UTF-8 278854:279002].
--   Monodromy.Counter.Reversible.Recording.table_arc at L5594-L5596 [UTF-8 279004:279167].
--   Monodromy.Counter.Reversible.Recording.copy_eq_iff at L5598-L5604 [UTF-8 279169:279485].
--   Monodromy.Counter.Reversible.Recording.finish_eq_iff at L5618-L5622 [UTF-8 279908:280149].
--   Monodromy.Counter.Reversible.Recording.extraOrigin_inc at L5625-L5629 [UTF-8 280152:280448].
--   Monodromy.Counter.Reversible.Recording.extraOrigin_dec at L5631-L5637 [UTF-8 280450:280813].
--   Monodromy.Counter.Reversible.Recording.extraDestination_inc at L5639-L5644 [UTF-8 280815:281150].
--   Monodromy.Counter.Reversible.Recording.extraDestination_dec at L5646-L5654 [UTF-8 281152:281608].
--   Monodromy.Counter.Reversible.Recording.extraOperation_dec at L5662-L5670 [UTF-8 281909:282350].
--   Monodromy.Counter.Reversible.Recording.extraOrigin_row at L5672-L5685 [UTF-8 282352:282916].
--   Monodromy.Counter.Reversible.Recording.extra_deterministic at L5687-L5723 [UTF-8 282918:284775].
--   Monodromy.Counter.Reversible.Recording.extraDestination_injective at L5725-L5746 [UTF-8 284777:285995].
--   Monodromy.Counter.Reversible.Recording.extraOrigin_shape at L5748-L5760 [UTF-8 285997:286652].
--   Monodromy.Counter.Reversible.Recording.extraDestination_shape at L5762-L5780 [UTF-8 286654:287549].
--   Monodromy.Counter.Reversible.Recording.packing_extra_source_ne at L5782-L5792 [UTF-8 287551:288147].
--   Monodromy.Counter.Reversible.Recording.packing_extra_target_ne at L5794-L5804 [UTF-8 288149:288777].
--   Monodromy.Counter.Reversible.Recording.deterministic at L5806-L5823 [UTF-8 288779:289986].
--   Monodromy.Counter.Reversible.Recording.targetCompatible at L5825-L5842 [UTF-8 289988:291179].
--   Monodromy.Counter.Reversible.Recording.frame at L5845-L5846 [UTF-8 291182:291340].
--   Monodromy.Counter.Reversible.Recording.framed at L5848-L5849 [UTF-8 291342:291502].
--   Monodromy.Counter.Reversible.Recording.encode at L5851-L5852 [UTF-8 291504:291648].
--   Monodromy.Counter.Reversible.Recording.embed at L5928-L5929 [UTF-8 295552:295660].
--   Monodromy.Counter.Reversible.Recording.OldNonnegative at L6050-L6051 [UTF-8 301893:302008].
--   Monodromy.Counter.Reversible.Recording.admissible at L6053-L6061 [UTF-8 302010:302522].
--   Monodromy.Counter.Reversible.Recording.Valid at L6063-L6064 [UTF-8 302524:302693].
--   Monodromy.Counter.Reversible.Recording.valid_mid_iff at L6072-L6080 [UTF-8 303061:303515].
--   Monodromy.Counter.Reversible.Recording.Boundary at L6272-L6274 [UTF-8 313652:313822].
--   Monodromy.Counter.Reversible.Recording.InternalStep at L6276-L6278 [UTF-8 313824:313987].
--   Monodromy.Counter.Reversible.Recording.InternalReaches at L6280-L6281 [UTF-8 313989:314093].
--   Monodromy.Counter.Reversible.Recording.FirstReturn at L6283-L6287 [UTF-8 314095:314405].
--   Monodromy.Counter.Reversible.Recording.Marked at L6526-L6527 [UTF-8 328195:328326].
--   Monodromy.Counter.Reversible.Recording.instDecidableMarked at L6529-L6530 [UTF-8 328328:328512].
--   Monodromy.Counter.Reversible.Recording.InternalMarkedStep at L6547-L6549 [UTF-8 329090:329286].
--   Monodromy.Counter.Reversible.Recording.InternalMarkedReaches at L6551-L6552 [UTF-8 329288:329433].
--   Monodromy.Counter.Reversible.Recording.MarkedFirstReturn at L6554-L6557 [UTF-8 329435:329714].
--   Monodromy.Counter.Reversible.PrimeCompression.HasSource at L6667-L6668 [UTF-8 335344:335461].
--   Monodromy.Counter.Reversible.PrimeCompression.instDecidableHasSource at L6670-L6671 [UTF-8 335463:335638].
--   Monodromy.Counter.Reversible.PrimeCompression.HasRestore at L6673-L6675 [UTF-8 335640:335852].
--   Monodromy.Counter.Reversible.PrimeCompression.instDecidableHasRestore at L6677-L6679 [UTF-8 335854:336124].
--   Monodromy.Counter.Reversible.PrimeCompression.SourceSite at L6681-L6681 [UTF-8 336126:336217].
--   Monodromy.Counter.Reversible.PrimeCompression.RestoreSite at L6682-L6682 [UTF-8 336218:336311].
--   Monodromy.Counter.Reversible.PrimeCompression.HaltSite at L6683-L6683 [UTF-8 336312:336404].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceEdge at L6685-L6686 [UTF-8 336406:336552].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceEdge_spec at L6688-L6689 [UTF-8 336554:336716].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreEdge at L6691-L6693 [UTF-8 336718:336960].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreEdge_spec at L6695-L6699 [UTF-8 336962:337254].
--   Monodromy.Counter.Reversible.PrimeCompression.actionRegister at L6701-L6703 [UTF-8 337256:337362].
--   Monodromy.Counter.Reversible.PrimeCompression.Module at L6705-L6705 [UTF-8 337364:337444].
--   Monodromy.Counter.Reversible.PrimeCompression.moduleRegister at L6707-L6709 [UTF-8 337446:337660].
--   Monodromy.Counter.Reversible.PrimeCompression.modulus at L6711-L6712 [UTF-8 337662:337801].
--   Monodromy.Counter.Reversible.PrimeCompression.instNeZeroNatModulus at L6714-L6715 [UTF-8 337803:337963].
--   Monodromy.Counter.Reversible.PrimeCompression.reversed at L6717-L6721 [UTF-8 337965:338187].
--   Monodromy.Counter.Reversible.PrimeCompression.componentTable at L6723-L6726 [UTF-8 338189:338520].
--   Monodromy.Counter.Reversible.PrimeCompression.component_deterministic at L6728-L6733 [UTF-8 338522:338822].
--   Monodromy.Counter.Reversible.PrimeCompression.component_targetCompatible at L6735-L6740 [UTF-8 338824:339133].
--   Monodromy.Counter.Reversible.PrimeCompression.RawPart at L6742-L6743 [UTF-8 339135:339277].
--   Monodromy.Counter.Reversible.PrimeCompression.RawNode at L6745-L6746 [UTF-8 339279:339390].
--   Monodromy.Counter.Reversible.PrimeCompression.RawArc at L6748-L6749 [UTF-8 339392:339534].
--   Monodromy.Counter.Reversible.PrimeCompression.rawSize at L6751-L6752 [UTF-8 339536:339645].
--   Monodromy.Counter.Reversible.PrimeCompression.rawEdges at L6754-L6755 [UTF-8 339647:339756].
--   Monodromy.Counter.Reversible.PrimeCompression.rawNodeEquiv at L6757-L6758 [UTF-8 339758:339905].
--   Monodromy.Counter.Reversible.PrimeCompression.rawArcEquiv at L6760-L6761 [UTF-8 339907:340053].
--   Monodromy.Counter.Reversible.PrimeCompression.moduleNode at L6763-L6765 [UTF-8 340055:340296].
--   Monodromy.Counter.Reversible.PrimeCompression.haltNode at L6767-L6768 [UTF-8 340298:340460].
--   Monodromy.Counter.Reversible.PrimeCompression.moduleNode_injective at L6770-L6772 [UTF-8 340462:340710].
--   Monodromy.Counter.Reversible.PrimeCompression.haltNode_injective at L6774-L6776 [UTF-8 340712:340904].
--   Monodromy.Counter.Reversible.PrimeCompression.haltNode_ne_moduleNode at L6778-L6784 [UTF-8 340906:341281].
--   Monodromy.Counter.Reversible.PrimeCompression.rawEdge at L6786-L6788 [UTF-8 341283:341501].
--   Monodromy.Counter.Reversible.PrimeCompression.rawTable at L6790-L6792 [UTF-8 341503:341706].
--   Monodromy.Counter.Reversible.PrimeCompression.rawTable_arc at L6794-L6797 [UTF-8 341708:341929].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_deterministic at L6799-L6814 [UTF-8 341931:342938].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_targetCompatible at L6816-L6831 [UTF-8 342940:343956].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceInputPosition at L6833-L6836 [UTF-8 343958:344275].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceInput at L6838-L6840 [UTF-8 344277:344484].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceShiftOutput at L6842-L6846 [UTF-8 344486:344833].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreInput at L6848-L6850 [UTF-8 344835:345084].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreOutput at L6852-L6854 [UTF-8 345086:345272].
--   Monodromy.Counter.Reversible.PrimeCompression.boundary at L6856-L6860 [UTF-8 345274:345624].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceInput_injective at L6870-L6877 [UTF-8 346094:346596].
--   Monodromy.Counter.Reversible.PrimeCompression.boundary_injective at L6879-L6892 [UTF-8 346598:347549].
--   Monodromy.Counter.Reversible.PrimeCompression.component_no_incoming_sourceInput at L6894-L6900 [UTF-8 347551:348015].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_no_incoming_boundary at L6902-L6921 [UTF-8 348017:349431].
--   Monodromy.Counter.Reversible.PrimeCompression.moduleNode_module at L6923-L6932 [UTF-8 349433:350004].
--   Monodromy.Counter.Reversible.PrimeCompression.moduleNode_position at L6934-L6942 [UTF-8 350006:350557].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_no_outgoing_moduleNode at L6944-L6955 [UTF-8 350559:351326].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_no_incoming_moduleNode at L6957-L6968 [UTF-8 351328:352096].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_no_outgoing_sourceShiftOutput at L6970-L6981 [UTF-8 352098:352863].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_no_outgoing_sourceFinish at L6983-L6992 [UTF-8 352865:353560].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_no_outgoing_restoreOutput at L6994-L6999 [UTF-8 353562:353937].
--   Monodromy.Counter.Reversible.PrimeCompression.raw_no_incoming_restoreInput at L7001-L7008 [UTF-8 353939:354418].
--   Monodromy.Counter.Reversible.PrimeCompression.radix_entry_ne_finish at L7010-L7013 [UTF-8 354420:354590].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceNode_ne_boundary at L7015-L7028 [UTF-8 354592:355554].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceShiftOutput_ne_boundary at L7030-L7038 [UTF-8 355556:355963].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceFinish_ne_boundary at L7040-L7047 [UTF-8 355965:356487].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreOutput_ne_boundary at L7049-L7057 [UTF-8 356489:356994].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceNode_ne_restoreInput at L7059-L7064 [UTF-8 356996:357424].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceShiftOutput_ne_restoreInput at L7066-L7070 [UTF-8 357426:357791].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceFinish_ne_restoreInput at L7072-L7076 [UTF-8 357793:358230].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreOutput_ne_restoreInput at L7078-L7084 [UTF-8 358232:358703].
--   Monodromy.Counter.Reversible.PrimeCompression.shift_owner_unique at L7086-L7096 [UTF-8 358705:359360].
--   Monodromy.Counter.Reversible.PrimeCompression.test_owner_alternative at L7098-L7113 [UTF-8 359362:360301].
--   Monodromy.Counter.Reversible.PrimeCompression.test_owner_form at L7115-L7126 [UTF-8 360303:361004].
--   Monodromy.Counter.Reversible.PrimeCompression.testSelected at L7139-L7141 [UTF-8 361741:362000].
--   Monodromy.Counter.Reversible.PrimeCompression.testSelected_iff at L7143-L7147 [UTF-8 362002:362270].
--   Monodromy.Counter.Reversible.PrimeCompression.test_matching at L7149-L7160 [UTF-8 362272:363033].
--   Monodromy.Counter.Reversible.PrimeCompression.source_test_matching at L7162-L7166 [UTF-8 363035:363367].
--   Monodromy.Counter.Reversible.PrimeCompression.target_test_matching at L7168-L7172 [UTF-8 363369:363698].
--   Monodromy.Counter.Reversible.PrimeCompression.ShiftConnection at L7202-L7208 [UTF-8 365340:365757].
--   Monodromy.Counter.Reversible.PrimeCompression.RestoreConnection at L7210-L7214 [UTF-8 365759:366087].
--   Monodromy.Counter.Reversible.PrimeCompression.TestConnection at L7216-L7227 [UTF-8 366089:366930].
--   Monodromy.Counter.Reversible.PrimeCompression.Connection at L7229-L7233 [UTF-8 366932:367250].
--   Monodromy.Counter.Reversible.PrimeCompression.instDecidableRelFinRawSizeConnection at L7235-L7239 [UTF-8 367252:367467].
--   Monodromy.Counter.Reversible.PrimeCompression.sourceShiftOutput_injective at L7241-L7244 [UTF-8 367469:367709].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreOutput_injective at L7246-L7249 [UTF-8 367711:367943].
--   Monodromy.Counter.Reversible.PrimeCompression.source_restore_disjoint at L7251-L7257 [UTF-8 367945:368390].
--   Monodromy.Counter.Reversible.PrimeCompression.selected_source_form at L7259-L7267 [UTF-8 368392:368995].
--   Monodromy.Counter.Reversible.PrimeCompression.shift_test_disjoint at L7269-L7281 [UTF-8 368997:369814].
--   Monodromy.Counter.Reversible.PrimeCompression.test_connection_functional at L7283-L7308 [UTF-8 369816:371366].
--   Monodromy.Counter.Reversible.PrimeCompression.connection_functional at L7310-L7344 [UTF-8 371368:373587].
--   Monodromy.Counter.Reversible.PrimeCompression.boundary_ne_restoreInput at L7346-L7355 [UTF-8 373589:374197].
--   Monodromy.Counter.Reversible.PrimeCompression.shift_connection_backward at L7357-L7376 [UTF-8 374199:375485].
--   Monodromy.Counter.Reversible.PrimeCompression.shift_restore_disjoint at L7378-L7389 [UTF-8 375487:376260].
--   Monodromy.Counter.Reversible.PrimeCompression.test_connection_backward at L7391-L7423 [UTF-8 376262:378220].
--   Monodromy.Counter.Reversible.PrimeCompression.connection_backward at L7425-L7456 [UTF-8 378222:380274].
--   Monodromy.Counter.Reversible.PrimeCompression.selected_forward at L7458-L7466 [UTF-8 380276:380855].
--   Monodromy.Counter.Reversible.PrimeCompression.connection_source_free at L7468-L7480 [UTF-8 380857:381745].
--   Monodromy.Counter.Reversible.PrimeCompression.connection_target_free at L7482-L7492 [UTF-8 381747:382468].
--   Monodromy.Counter.Reversible.PrimeCompression.boundary_unconnected at L7494-L7507 [UTF-8 382470:383359].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreInput_unconnected at L7509-L7520 [UTF-8 383361:384206].
--   Monodromy.Counter.Reversible.PrimeCompression.connection_terminal at L7522-L7533 [UTF-8 384208:385008].
--   Monodromy.Counter.Reversible.PrimeCompression.wiring at L7535-L7544 [UTF-8 385010:385627].
--   Monodromy.Counter.Reversible.PrimeCompression.size at L7546-L7548 [UTF-8 385629:385845].
--   Monodromy.Counter.Reversible.PrimeCompression.table at L7550-L7554 [UTF-8 385847:386221].
--   Monodromy.Counter.Reversible.PrimeCompression.deterministic at L7556-L7559 [UTF-8 386223:386523].
--   Monodromy.Counter.Reversible.PrimeCompression.targetCompatible at L7561-L7564 [UTF-8 386525:386837].
--   Monodromy.Counter.Reversible.PrimeCompression.encode at L7574-L7579 [UTF-8 387442:387914].
--   Monodromy.Counter.Reversible.PrimeCompression.siteOfEdge at L7644-L7645 [UTF-8 391966:392081].
--   Monodromy.Counter.Reversible.PrimeCompression.restoreOfTest at L7647-L7649 [UTF-8 392083:392313].
--   Monodromy.Counter.Reversible.PrimeCompression.Boundary at L7835-L7840 [UTF-8 404057:404481].
--   Monodromy.Counter.Reversible.PrimeCompression.MappedState at L7842-L7848 [UTF-8 404483:404989].
--   Monodromy.Counter.Reversible.PrimeCompression.InternalStep at L7850-L7855 [UTF-8 404991:405450].
--   Monodromy.Counter.Reversible.PrimeCompression.InternalReaches at L7857-L7859 [UTF-8 405452:405687].
--   Monodromy.Counter.Reversible.PrimeCompression.FirstReturn at L7861-L7868 [UTF-8 405689:406276].
--   Monodromy.Counter.Reversible.PrimeCompression.naturalState at L8157-L8159 [UTF-8 424745:424948].
--   Monodromy.Counter.Reversible.PrimeCompression.toNatural at L8254-L8255 [UTF-8 430203:430319].
--   Monodromy.Counter.Reversible.PrimeCompression.Marked at L8308-L8313 [UTF-8 433605:434084].
--   Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedStep at L8338-L8342 [UTF-8 435366:435765].
--   Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedReaches at L8344-L8346 [UTF-8 435767:436043].
--   Monodromy.Counter.Reversible.PrimeCompression.MarkedFirstReturn at L8348-L8354 [UTF-8 436045:436592].
--   Monodromy.ReversibleCompilation.markSource at L8447-L8451 [UTF-8 441823:442066].
--   Monodromy.ReversibleCompilation.markedProgram at L8458-L8461 [UTF-8 442263:442602].
--   Monodromy.ReversibleCompilation.MarkedBoundary at L8468-L8471 [UTF-8 442906:443226].
--   Monodromy.ReversibleCompilation.NativeInternalStep at L8501-L8504 [UTF-8 444929:445250].
--   Monodromy.ReversibleCompilation.NativeInternalReaches at L8506-L8508 [UTF-8 445252:445490].
--   Monodromy.ReversibleCompilation.NativeFirstReturn at L8510-L8515 [UTF-8 445492:445955].
--   Monodromy.ReversibleCompilation.nativeMacro at L8616-L8621 [UTF-8 452319:452792].

-- Generated by Lean-fact skeleton subtraction; original source is frozen in imports/monodromy/source.
module
public import Definitions.Def_Monodromy_Continuation
public import Definitions.Def_Monodromy_Tape
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


/-!
# Counter machines and native continuation

The standard finite counter semantics is retained. A three-phase finite
compiler realizes each two-counter step by two actual geometric returns;
the faithful configuration encoding preserves complete partial execution.

Classical finite counter macros and prime coding compile an entire finite
Turing table through three source registers to the same two-counter target.
Every arithmetic loop has a separate finite control region, with marked
source entries and no intermediate return boundary.
-/

@[expose] public section

namespace Monodromy.Counter

inductive Instruction (n m : ℕ)
  | inc (reg : Fin n) (next : Fin m)
  | dec (reg : Fin n) (zero nonzero : Fin m)
  | halt

structure Configuration (n m : ℕ) where
  pc : Fin m
  counters : Fin n → ℕ

abbrev Program (n m : ℕ) := Fin m → Instruction n m

def step {n m : ℕ} (program : Program n m)
    (state : Configuration n m) : Option (Configuration n m) :=
  match program state.pc with
  | .inc reg next =>
      some ⟨next, Function.update state.counters reg (state.counters reg + 1)⟩
  | .dec reg zero nonzero =>
      match state.counters reg with
      | 0 => some ⟨zero, state.counters⟩
      | value + 1 => some ⟨nonzero, Function.update state.counters reg value⟩
  | .halt => none

variable {n m : ℕ} (program : Program n m) (state : Configuration n m)









/-- Partial evaluation retains the last state when its instruction halts. -/
def eval {n m : ℕ} (program : Program n m) : Configuration n m → Part (Configuration n m) :=
  StateTransition.eval (step program)

/-- The total return map keeps a halted configuration in place. -/
def tick {n m : ℕ} (program : Program n m) (state : Configuration n m) : Configuration n m :=
  (step program state).getD state



variable {k : ℕ}

/-- Rename every program address while retaining the registers. -/
def mapInstruction (address : Fin m → Fin k) : Instruction n m → Instruction n k
  | .inc register target => .inc register (address target)
  | .dec register zero nonzero => .dec register (address zero) (address nonzero)
  | .halt => .halt

def mapConfiguration (address : Fin m → Fin k) (state : Configuration n m) :
    Configuration n k := ⟨address state.pc, state.counters⟩







end Monodromy.Counter

noncomputable section

namespace Monodromy.CounterContinuation

open CoupledContinuation

/-- Three finite program phases share the existing upper control coordinate. -/
def label {m : ℕ} (position : Fin m) (phase : Fin 3) : ℤ :=
  (finProdFinEquiv (position, phase)).val



def memoryGate (register : Fin 2) : Gate := if register = 0 then .left else .right

def zeroGate (register : Fin 2) : Gate := if register = 0 then .zeroLeft else .zeroRight

def instructionWord {m : ℕ} (program : Counter.Program 2 m) (position : Fin m) (phase : Fin 3) : Word :=
  match program position with
  | .halt => []
  | .inc register target =>
      if phase = 0 then Word.control 1
      else if phase = 1 then
        Word.atom (memoryGate register) ++ Word.control (label target 0 - label position 1)
      else []
  | .dec register zero nonzero =>
      if phase = 0 then Word.control 1 ++ Word.atom (zeroGate register)
      else if phase = 1 then
        Word.atom (memoryGate register) true ++ Word.control (label nonzero 0 - label position 1)
      else Word.control (label zero 0 - label position 2)

def instructionStop {m : ℕ} (instruction : Counter.Instruction 2 m) : Bool :=
  match instruction with | .halt => true | _ => false

def stopping {m : ℕ} (program : Counter.Program 2 m) (position : Fin m) (phase : Fin 3) : Bool :=
  if phase = 0 then instructionStop (program position) else false

def wordTable {m : ℕ} (program : Counter.Program 2 m) (index : Fin (m * 3)) : Word :=
  let address := finProdFinEquiv.symm index
  instructionWord program address.1 address.2

def stopTable {m : ℕ} (program : Counter.Program 2 m) (index : Fin (m * 3)) : Bool :=
  let address := finProdFinEquiv.symm index
  stopping program address.1 address.2

def compile {m : ℕ} (program : Counter.Program 2 m) : CoupledContinuation.Program (m * 3) :=
  ⟨wordTable program, stopTable program⟩

def encode {m : ℕ} (state : Counter.Configuration 2 m) : Memory :=
  prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)





variable {m : ℕ} [NeZero m]





end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ} [NeZero m]

















end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ}



variable [NeZero m]













end Monodromy.CounterContinuation


namespace Monodromy.CounterContinuation

variable {m : ℕ} [NeZero m]



end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

/-- A source boundary is observed from the actual cubic control root alone. -/
def SourceBoundary (state : Memory) : Prop := controlRoot 3 state = 1







variable {m : ℕ} [NeZero m]







end Monodromy.CounterContinuation

namespace Monodromy.PrimeCode

/-- A finite family of distinct primes represents independent natural registers. -/
structure Basis (n : ℕ) where
  prime : Fin n → ℕ
  isPrime : ∀ index, (prime index).Prime
  distinct : Function.Injective prime

namespace Basis

variable {n : ℕ} (basis : Basis n)

def encode (registers : Fin n → ℕ) : ℕ := ∏ index, basis.prime index ^ registers index

def decode (code : ℕ) : Fin n → ℕ := fun index => code.factorization (basis.prime index)





















end Basis

/-- A classical proof-side encoding of three source registers, using fixed distinct primes. -/
def prime (index : Fin 3) : ℕ := if index = 0 then 2 else if index = 1 then 3 else 5

def encode (registers : Fin 3 → ℕ) : ℕ :=
  2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2

theorem prime_prime (index : Fin 3) : (prime index).Prime := by
  fin_cases index <;> norm_num [prime] <;> decide

def decode (code : ℕ) : Fin 3 → ℕ := fun index => code.factorization (prime index)

/-- The existing three-register code is the specialization with primes 2, 3 and 5. -/
def three : Basis 3 where
  prime := prime
  isPrime := prime_prime
  distinct := by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all [prime]



























end Monodromy.PrimeCode

namespace Monodromy.Counter.RegisterRelocation

variable {n k m : ℕ}

def instruction (register : Fin n → Fin k) : Instruction n m → Instruction k m
  | .inc source target => .inc (register source) target
  | .dec source zero nonzero => .dec (register source) zero nonzero
  | .halt => .halt

def program (register : Fin n → Fin k) (source : Program n m) : Program k m :=
  fun address => instruction register (source address)

/-- Registers outside the image retain their arbitrary fixed background values. -/
def embed (register : Fin n → Fin k) (background : Fin k → ℕ)
    (state : Configuration n m) : Configuration k m :=
  ⟨state.pc, Function.extend register state.counters background⟩











/-- Either stack and the shared third scratch register can host the same two-register macro. -/
def pairIntoThree (active : Fin 2) (index : Fin 2) : Fin 3 :=
  if index = 0 then active.castSucc else 2



end Monodromy.Counter.RegisterRelocation

namespace Monodromy.Counter

variable {n m k : ℕ}





end Monodromy.Counter

namespace Monodromy.CounterMultiplication

/-- Countdown cells are only finite control addresses, never another register. -/
def phase (factor remaining : ℕ) : Fin (factor + 4) :=
  ⟨remaining % (factor + 4), Nat.mod_lt _ (by omega)⟩

def transfer (factor : ℕ) : Fin (factor + 4) := ⟨factor + 1, by omega⟩
def restore (factor : ℕ) : Fin (factor + 4) := ⟨factor + 2, by omega⟩
def finish (factor : ℕ) : Fin (factor + 4) := ⟨factor + 3, by omega⟩

def program (factor : ℕ) : Counter.Program 2 (factor + 4) := fun position =>
  if position.val = 0 then .dec 0 (transfer factor) (phase factor factor)
  else if position.val ≤ factor then .inc 1 (phase factor (position.val - 1))
  else if position.val = factor + 1 then .dec 1 (finish factor) (restore factor)
  else if position.val = factor + 2 then .inc 0 (transfer factor)
  else .halt

def configuration (factor : ℕ) (position : Fin (factor + 4)) (first second : ℕ) :
    Counter.Configuration 2 (factor + 4) := ⟨position, ![first, second]⟩







































end Monodromy.CounterMultiplication

namespace Monodromy.Counter.DivMod

variable (p : ℕ) [NeZero p]

/-- Four bounded-remainder phases and one quotient-increment address. -/
def size : ℕ := 4 * p + 1

def consume (remainder : Fin p) : Fin (size p) := ⟨remainder.val, by dsimp [size]; omega⟩
def transfer (remainder : Fin p) : Fin (size p) := ⟨p + remainder.val, by dsimp [size]; omega⟩
def restore (remainder : Fin p) : Fin (size p) := ⟨2 * p + remainder.val, by dsimp [size]; omega⟩
def finish (remainder : Fin p) : Fin (size p) := ⟨3 * p + remainder.val, by dsimp [size]; omega⟩
def bump : Fin (size p) := ⟨4 * p, by dsimp [size]; omega⟩

def next (remainder : Fin p) : Fin (size p) :=
  if bound : remainder.val + 1 < p then consume p ⟨remainder.val + 1, bound⟩ else bump p

/-- Division is implemented by a static finite inc/dec/halt table. -/
def program : Counter.Program 2 (size p) := fun address =>
  if first : address.val < p then
    .dec 0 (transfer p ⟨address.val, first⟩) (next p ⟨address.val, first⟩)
  else if second : address.val < 2 * p then
    .dec 1 (finish p ⟨address.val - p, by omega⟩) (restore p ⟨address.val - p, by omega⟩)
  else if third : address.val < 3 * p then
    .inc 0 (transfer p ⟨address.val - 2 * p, by omega⟩)
  else if address.val < 4 * p then .halt
  else .inc 1 (consume p 0)











/-- The only unbounded storage is the same pair of natural-number counters. -/
def configuration (address : Fin (size p)) (first second : ℕ) : Counter.Configuration 2 (size p) :=
  ⟨address, ![first, second]⟩



















def residue (value : ℕ) : Fin p :=
  ⟨value % p, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))⟩




















end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]

/-- The program contains only the two already checked finite arithmetic tables. -/
def size : ℕ := Counter.DivMod.size p + (p + 4)

def divBlock (address : Fin (Counter.DivMod.size p)) : Fin (size p) :=
  Fin.castAdd (p + 4) address

def mulAddress (address : Fin (p + 4)) : Fin (size p) :=
  Fin.natAdd (Counter.DivMod.size p) address

/-- Nonzero remainder exits enter the multiplier's existing bounded countdown. -/
def divAddress (address : Fin (Counter.DivMod.size p)) : Fin (size p) :=
  match Counter.DivMod.program p address with
  | .halt =>
      if address.val = 3 * p then divBlock p address
      else mulAddress p (CounterMultiplication.phase p (address.val - 3 * p))
  | _ => divBlock p address

def entry : Fin (size p) := divAddress p (Counter.DivMod.consume p 0)
def success : Fin (size p) := divBlock p (Counter.DivMod.finish p 0)
def failure : Fin (size p) := mulAddress p (CounterMultiplication.finish p)

/-- Rewired finite program counters provide the conditional; the instructions remain inc/dec/halt. -/
def program : Counter.Program 2 (size p) :=
  Fin.addCases
    (fun address => Counter.mapInstruction (divAddress p) (Counter.DivMod.program p address))
    (fun address => Counter.mapInstruction (mulAddress p) (CounterMultiplication.program p address))

def configuration (address : Fin (size p)) (first second : ℕ) : Counter.Configuration 2 (size p) :=
  ⟨address, ![first, second]⟩













































end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]

def base : ℕ := a + 1
instance base_neZero : NeZero (base a) := ⟨by simp [base]⟩

abbrev Row := Fin q × Fin a
abbrev Phase := Unit ⊕ (Fin (base a + 4) ⊕ (Fin a ⊕ Fin (DivMod.size (base a))))
abbrev Address := Row a q × Phase a

def size : ℕ := Fintype.card (Address a q)

def address : Address a q ≃ Fin (size a q) := Fintype.equivFin _

def dispatch (row : Row a q) : Fin (size a q) := address a q (row, Sum.inl ())
def multiply (row : Row a q) (cell : Fin (base a + 4)) : Fin (size a q) :=
  address a q (row, Sum.inr (Sum.inl cell))
def add (row : Row a q) (remaining : Fin a) : Fin (size a q) :=
  address a q (row, Sum.inr (Sum.inr (Sum.inl remaining)))
def divide (row : Row a q) (cell : Fin (DivMod.size (base a))) : Fin (size a q) :=
  address a q (row, Sum.inr (Sum.inr (Sum.inr cell)))

omit [NeZero a] [NeZero q] in
@[simp] theorem address_dispatch (row : Row a q) :
    (address a q).symm (dispatch a q row) = (row, Sum.inl ()) :=
  (address a q).symm_apply_apply _






def counters (left right : ℕ) : Fin 3 → ℕ := ![left, right, 0]

def encode (state : TM0.Cfg (Fin a) (Fin q)) : Configuration 3 (size a q) :=
  ⟨dispatch a q (state.q, state.Tape.head),
    counters (TapeCode.encode state.Tape.left) (TapeCode.encode state.Tape.right)⟩



def pushRegister : Dir → Fin 2 | .left => 1 | .right => 0
def popRegister : Dir → Fin 2 | .left => 0 | .right => 1

def mulTarget (row : Row a q) (cell : Fin (base a + 4)) : Fin (size a q) :=
  if cell = CounterMultiplication.finish (base a) then add a q row row.2
  else multiply a q row cell

def symbol (remainder : Fin (base a)) : Fin a :=
  if bound : remainder.val < a then ⟨remainder.val, bound⟩ else 0

def divTarget (row : Row a q) (target : Fin q)
    (cell : Fin (DivMod.size (base a))) : Fin (size a q) :=
  if terminal : ∃ remainder, cell = DivMod.finish (base a) remainder then
    dispatch a q (target, symbol a terminal.choose)
  else divide a q row cell





def previous (remaining : Fin a) : Fin a :=
  ⟨remaining.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) remaining.isLt⟩

def body (machine : TM0.Machine (Fin a) (Fin q)) (location : Address a q) :
    Instruction 3 (size a q) :=
  let row := location.1
  match machine row.1 row.2 with
  | none => .halt
  | some (target, .write value) =>
      match location.2 with
      | .inl () => .dec 2 (dispatch a q (target, value)) (dispatch a q (target, value))
      | .inr _ => .halt
  | some (target, .move direction) =>
      match location.2 with
      | .inl () => .dec 2 (mulTarget a q row 0) (mulTarget a q row 0)
      | .inr (.inl cell) =>
          mapInstruction (mulTarget a q row)
            (RegisterRelocation.instruction
              (RegisterRelocation.pairIntoThree (pushRegister direction))
              (CounterMultiplication.program (base a) cell))
      | .inr (.inr (.inl remaining)) =>
          if remaining.val = 0 then
            .dec 2 (divTarget a q row target (DivMod.consume (base a) 0))
              (divTarget a q row target (DivMod.consume (base a) 0))
          else .inc (pushRegister direction).castSucc (add a q row (previous a remaining))
      | .inr (.inr (.inr cell)) =>
          mapInstruction (divTarget a q row target)
            (RegisterRelocation.instruction
              (RegisterRelocation.pairIntoThree (popRegister direction))
              (DivMod.program (base a) cell))

def program (machine : TM0.Machine (Fin a) (Fin q)) : Program 3 (size a q) :=
  fun cell => body a q machine ((address a q).symm cell)

@[simp] theorem program_dispatch (machine : TM0.Machine (Fin a) (Fin q)) (row : Row a q) :
    program a q machine (dispatch a q row) =
      match machine row.1 row.2 with
      | none => .halt
      | some (target, .write value) =>
          .dec 2 (dispatch a q (target, value)) (dispatch a q (target, value))
      | some (_, .move _) => .dec 2 (mulTarget a q row 0) (mulTarget a q row 0) := by
  simp only [program, address_dispatch, body]





/-- A marked source boundary is determined by the finite program counter alone. -/
def Boundary (cell : Fin (size a q)) : Prop := ∃ row, cell = dispatch a q row









/-- Internal arithmetic transitions exclude dispatch cells at their source. -/
def InternalStep (machine : TM0.Machine (Fin a) (Fin q))
    (first last : Configuration 3 (size a q)) : Prop :=
  step (program a q machine) first = some last ∧ ¬ Boundary a q first.pc

abbrev InternalReaches (machine : TM0.Machine (Fin a) (Fin q)) :=
  Relation.ReflTransGen (InternalStep a q machine)







def frame (active : Fin 2) (first spectator : ℕ) : Fin 3 → ℕ :=
  if active = 0 then counters first spectator else counters spectator first

















/-- One dispatch edge followed by arithmetic steps whose sources are all unmarked. -/
def FirstReturn (machine : TM0.Machine (Fin a) (Fin q))
    (first last : Configuration 3 (size a q)) : Prop :=
  ∃ after, step (program a q machine) first = some after ∧
    InternalReaches a q machine after last













end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}

instance prime_neZero (register : Fin 3) : NeZero (PrimeCode.prime register) :=
  ⟨(PrimeCode.prime_prime register).ne_zero⟩

def blockSize : Instruction 3 m → ℕ
  | .inc register _ => PrimeCode.prime register + 4
  | .dec register _ _ => CounterPrimeProbe.size (PrimeCode.prime register)
  | .halt => 0

abbrev Address (source : Program 3 m) := Σ row : Fin m, Unit ⊕ Fin (blockSize (source row))

def size (source : Program 3 m) : ℕ := Fintype.card (Address source)
def address (source : Program 3 m) : Address source ≃ Fin (size source) := Fintype.equivFin _

def dispatch (source : Program 3 m) (row : Fin m) : Fin (size source) :=
  address source ⟨row, .inl ()⟩

def multiply (source : Program 3 m) (row : Fin m) (register : Fin 3) (next : Fin m)
    (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) : Fin (size source) :=
  address source ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩

def probe (source : Program 3 m) (row : Fin m) (register : Fin 3) (zero nonzero : Fin m)
    (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) : Fin (size source) :=
  address source ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩









def mulTarget (source : Program 3 m) (row : Fin m) (register : Fin 3) (next : Fin m)
    (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) : Fin (size source) :=
  if cell = CounterMultiplication.finish (PrimeCode.prime register) then dispatch source next
  else multiply source row register next selected cell

def probeTarget (source : Program 3 m) (row : Fin m) (register : Fin 3) (zero nonzero : Fin m)
    (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) : Fin (size source) :=
  if cell = CounterPrimeProbe.success (PrimeCode.prime register) then dispatch source nonzero
  else if cell = CounterPrimeProbe.failure (PrimeCode.prime register) then dispatch source zero
  else probe source row register zero nonzero selected cell







def body (source : Program 3 m) (location : Address source) : Instruction 2 (size source) :=
  match selected : source location.1 with
  | .halt => .halt
  | .inc register next =>
      match location.2 with
      | .inl () =>
          .dec 1 (mulTarget source location.1 register next selected 0)
            (mulTarget source location.1 register next selected 0)
      | .inr cell =>
          mapInstruction (mulTarget source location.1 register next selected)
            (CounterMultiplication.program (PrimeCode.prime register)
              (cell.cast (by simp [blockSize, selected])))
  | .dec register zero nonzero =>
      match location.2 with
      | .inl () =>
          .dec 1 (probeTarget source location.1 register zero nonzero selected
            (CounterPrimeProbe.entry (PrimeCode.prime register)))
            (probeTarget source location.1 register zero nonzero selected
              (CounterPrimeProbe.entry (PrimeCode.prime register)))
      | .inr cell =>
          mapInstruction (probeTarget source location.1 register zero nonzero selected)
            (CounterPrimeProbe.program (PrimeCode.prime register)
              (cell.cast (by simp [blockSize, selected])))

def program (source : Program 3 m) : Program 2 (size source) :=
  fun cell => body source ((address source).symm cell)







def encode (source : Program 3 m) (state : Configuration 3 m) : Configuration 2 (size source) :=
  ⟨dispatch source state.pc, ![PrimeCode.encode state.counters, 0]⟩



def Boundary (source : Program 3 m) (cell : Fin (size source)) : Prop :=
  ∃ row, cell = dispatch source row








/-- Only dispatch cells are source boundaries; the scratch counter is never inspected here. -/
def InternalStep (source : Program 3 m)
    (first last : Configuration 2 (size source)) : Prop :=
  step (program source) first = some last ∧ ¬ Boundary source first.pc

abbrev InternalReaches (source : Program 3 m) :=
  Relation.ReflTransGen (InternalStep source)






















/-- One dispatch transition followed by a path containing no intermediate source boundary. -/
def FirstReturn (source : Program 3 m) (first last : Configuration 2 (size source)) : Prop :=
  ∃ after, step (program source) first = some after ∧ InternalReaches source after last





















end Monodromy.Counter.Compression

namespace Monodromy.Counter.EntryDispatch

variable {a m : ℕ}

/-- Prefix addresses contain only jumps through an already-zero workspace counter. -/
def program (source : Program 2 m) (entries : Fin a → Fin m) : Program 2 (a + m) :=
  Fin.addCases
    (fun symbol => .dec 1 (Fin.natAdd a (entries symbol)) (Fin.natAdd a (entries symbol)))
    (fun cell => mapInstruction (Fin.natAdd a) (source cell))

def entryState (symbol : Fin a) (registers : Fin 2 → ℕ) : Configuration 2 (a + m) :=
  ⟨Fin.castAdd m symbol, registers⟩



















end Monodromy.Counter.EntryDispatch

/-!
## Locally reversible counter tables
-/

namespace Monodromy.Counter.Reversible

inductive Action (n : ℕ)
  | shift (reg : Fin n) (amount : ℤ)
  | test (reg : Fin n) (atZero : Bool)
  deriving DecidableEq

abbrev State (n q : ℕ) := Fin q × (Fin n → ℤ)

structure Edge (n q : ℕ) where
  source : Fin q
  target : Fin q
  action : Action n
  deriving DecidableEq

abbrev Table (n q e : ℕ) := Fin e → Edge n q

namespace Action

variable {n : ℕ}

def enabled : Action n → (Fin n → ℤ) → Prop
  | .shift _ _, _ => True
  | .test reg atZero, values => (values reg = 0) ↔ atZero = true

instance (action : Action n) (values : Fin n → ℤ) : Decidable (enabled action values) := by
  cases action <;> simp only [enabled] <;> infer_instance

def apply : Action n → (Fin n → ℤ) → (Fin n → ℤ)
  | .shift reg amount, values => Function.update values reg (values reg + amount)
  | .test _ _, values => values

/-- The elementary source family required by reversible counter compression. -/
def UnitShift : Action n → Prop
  | .shift _ amount => amount = 1 ∨ amount = -1
  | .test _ _ => True

/-- The only two different alternatives allowed at a common port. -/
def Compatible : Action n → Action n → Prop
  | .test first firstZero, .test second secondZero => first = second ∧ firstZero ≠ secondZero
  | _, _ => False









end Action

variable {n q e : ℕ}

namespace Edge

def enabled (edge : Edge n q) (state : State n q) : Prop :=
  edge.source = state.1 ∧ edge.action.enabled state.2

instance (edge : Edge n q) (state : State n q) : Decidable (edge.enabled state) :=
  inferInstanceAs (Decidable (edge.source = state.1 ∧ edge.action.enabled state.2))

def execute (edge : Edge n q) (state : State n q) : State n q :=
  (edge.target, edge.action.apply state.2)

end Edge

/-- Alternatives at the same source port have disjoint guards. -/
def Deterministic (table : Table n q e) : Prop :=
  ∀ first second, first ≠ second → (table first).source = (table second).source →
    Action.Compatible (table first).action (table second).action

/-- Alternatives at the same target port have disjoint, unchanged test data. -/
def TargetCompatible (table : Table n q e) : Prop :=
  ∀ first second, first ≠ second → (table first).target = (table second).target →
    Action.Compatible (table first).action (table second).action

/-- Every live address can move at every integer register valuation. -/
def Complete (table : Table n q e) : Prop :=
  ∀ state : State n q, (∃ index, (table index).source = state.1) →
    ∃ index, (table index).enabled state

/-- Relational source semantics, before selecting a finite edge index. -/
def StepRel (table : Table n q e) (first last : State n q) : Prop :=
  ∃ index, (table index).enabled first ∧ (table index).execute first = last







/-- Bounded finite search; this source executor is independent of native geometry. -/
def step (table : Table n q e) (state : State n q) : Option (State n q) :=
  if available : ∃ index, (table index).enabled state then
    some ((table (Fin.find (fun index => (table index).enabled state) available)).execute state)
  else none









namespace Action

def IsShift : Action n → Prop
  | .shift _ _ => True
  | .test _ _ => False

instance (action : Action n) : Decidable action.IsShift := by
  cases action <;> simp only [IsShift] <;> infer_instance

instance (first second : Action n) : Decidable (Compatible first second) := by
  cases first <;> cases second <;> simp only [Compatible] <;> infer_instance

theorem Compatible.one_enabled {first second : Action n}
    (compatible : Compatible first second) (values : Fin n → ℤ) :
    enabled first values ∨ enabled second values := by
  cases first with
  | shift => simp [Compatible] at compatible
  | test register firstZero =>
      cases second with
      | shift => simp [Compatible] at compatible
      | test other secondZero =>
          rcases compatible with ⟨rfl, different⟩
          by_cases zero : values register = 0 <;>
            cases firstZero <;> cases secondZero <;> simp_all [enabled]

theorem test_disabled (register : Fin n) (atZero : Bool) :
    ∃ values : Fin n → ℤ, ¬ enabled (.test register atZero) values := by
  cases atZero
  · exact ⟨fun _ => 0, by simp [enabled]⟩
  · exact ⟨fun _ => 1, by simp [enabled]⟩

end Action

/-- A live port is covered by one unconditional shift or two complementary tests. -/
def CoveredAt (table : Table n q e) (position : Fin q) : Prop :=
  (¬ ∃ index, (table index).source = position) ∨
  (∃ index, (table index).source = position ∧ (table index).action.IsShift) ∨
  ∃ first second, (table first).source = position ∧ (table second).source = position ∧
    Action.Compatible (table first).action (table second).action

instance (table : Table n q e) (position : Fin q) : Decidable (CoveredAt table position) :=
  inferInstanceAs (Decidable (
    (¬ ∃ index, (table index).source = position) ∨
    (∃ index, (table index).source = position ∧ (table index).action.IsShift) ∨
    ∃ first second, (table first).source = position ∧ (table second).source = position ∧
      Action.Compatible (table first).action (table second).action))

theorem complete_of_covered (table : Table n q e)
    (covered : ∀ position, CoveredAt table position) : Complete table := by
  intro state outgoing
  rcases covered state.1 with empty | ⟨index, source, shift⟩ | ⟨first, second, fs, ss, compatible⟩
  · exact False.elim (empty outgoing)
  · refine ⟨index, source, ?_⟩
    cases action : (table index).action with
    | shift => trivial
    | test => simp [Action.IsShift, action] at shift
  · rcases compatible.one_enabled state.2 with first_enabled | second_enabled
    · exact ⟨first, fs, first_enabled⟩
    · exact ⟨second, ss, second_enabled⟩

theorem covered_of_complete (table : Table n q e) (deterministic : Deterministic table)
    (complete : Complete table) : ∀ position, CoveredAt table position := by
  intro position
  by_cases outgoing : ∃ index, (table index).source = position
  · obtain ⟨index, source⟩ := outgoing
    cases action : (table index).action with
    | shift register amount =>
        exact Or.inr (Or.inl ⟨index, source, by simp [Action.IsShift, action]⟩)
    | test register atZero =>
        obtain ⟨values, disabled⟩ := Action.test_disabled register atZero
        obtain ⟨other, other_source, other_enabled⟩ :=
          complete (position, values) ⟨index, source⟩
        have different : index ≠ other := by
          intro same
          subst other
          exact disabled (action ▸ other_enabled)
        exact Or.inr (Or.inr ⟨index, other, source, other_source,
          deterministic index other different (source.trans other_source.symm)⟩)
  · exact Or.inl outgoing

/-- Semantic completeness of a deterministic table has a finite syntactic test. -/
theorem complete_iff_covered (table : Table n q e) (deterministic : Deterministic table) :
    Complete table ↔ ∀ position, CoveredAt table position :=
  ⟨covered_of_complete table deterministic, complete_of_covered table⟩

/-- All quantified positions and edge indices in the coverage criterion are finite. -/
def decideComplete (table : Table n q e) (deterministic : Deterministic table) :
    Decidable (Complete table) :=
  decidable_of_iff (∀ position, CoveredAt table position)
    (complete_iff_covered table deterministic).symm

/-- Complete partial execution retains the final halted source configuration. -/
def eval (table : Table n q e) : State n q → Part (State n q) :=
  StateTransition.eval (step table)

/-- Every syntactically live address has an enabled edge on the stated invariant. -/
def CompleteOn (table : Table n q e) (invariant : State n q → Prop) : Prop :=
  ∀ state, invariant state → (∃ edge, (table edge).source = state.1) →
    ∃ edge, (table edge).enabled state

/-- Every defined source step preserves the stated invariant. -/
def Stable (table : Table n q e) (invariant : State n q → Prop) : Prop :=
  ∀ ⦃first last⦄, invariant first → step table first = some last → invariant last





def reverseAction : Action n → Action n
  | .shift register amount => .shift register (-amount)
  | .test register atZero => .test register atZero









@[simp] theorem reverseAction_compatible (first second : Action n) :
    Action.Compatible (reverseAction first) (reverseAction second) ↔
      Action.Compatible first second := by
  cases first <;> cases second <;> rfl

namespace Action



end Action

def reverseEdge (edge : Edge n q) : Edge n q :=
  ⟨edge.target, edge.source, reverseAction edge.action⟩



def reverseTable (table : Table n q e) : Table n q e :=
  fun index => reverseEdge (table index)



theorem reverseTable_deterministic (table : Table n q e) (compatible : TargetCompatible table) :
    Deterministic (reverseTable table) := by
  intro first second different same
  exact (reverseAction_compatible _ _).mpr (compatible first second different same)

theorem reverseTable_targetCompatible (table : Table n q e) (deterministic : Deterministic table) :
    TargetCompatible (reverseTable table) := by
  intro first second different same
  exact (reverseAction_compatible _ _).mpr (deterministic first second different same)









end Monodromy.Counter.Reversible

/-!
## Static finite port matchings
-/

namespace Monodromy.ReversiblePorts

variable {q e : ℕ}

/-- This finite lookup depends only on the static table and a finite vertex. -/
def mate (owner : Fin e → Fin q) (active : Fin e → Bool) (vertex : Fin q) : Option (Fin e) :=
  if found : ∃ edge, active edge = true ∧ owner edge = vertex then
    some (Fin.find (fun edge => active edge = true ∧ owner edge = vertex) found)
  else none

def Matching (owner : Fin e → Fin q) (active : Fin e → Bool) : Prop :=
  ∀ first second, active first = true → active second = true →
    owner first = owner second → first = second

theorem mate_some (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (vertex : Fin q) (edge : Fin e) :
    mate owner active vertex = some edge ↔ active edge = true ∧ owner edge = vertex := by
  unfold mate
  split_ifs with found
  · constructor
    · intro same
      have chosen := Fin.find_spec found
      have equal_index := Option.some.inj same
      simpa only [equal_index] using chosen
    · intro selected
      apply congrArg some
      have chosen := Fin.find_spec found
      exact matching _ _ chosen.1 selected.1 (chosen.2.trans selected.2.symm)
  · constructor
    · simp
    · intro selected
      exact (found ⟨edge, selected⟩).elim

def exchange (owner : Fin e → Fin q) (active : Fin e → Bool) : Fin q ⊕ Fin e → Fin q ⊕ Fin e
  | .inl vertex => (mate owner active vertex).elim (.inl vertex) Sum.inr
  | .inr edge => if active edge then .inl (owner edge) else .inr edge

theorem exchange_involutive (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Function.Involutive (exchange owner active) := by
  intro port
  cases port with
  | inl vertex =>
      cases chosen : mate owner active vertex with
      | none => simp [exchange, chosen]
      | some edge =>
          obtain ⟨enabled, endpoint⟩ := (mate_some owner active matching vertex edge).mp chosen
          simp [exchange, chosen, enabled, endpoint]
  | inr edge =>
      cases selected : active edge with
      | false => simp [exchange, selected]
      | true =>
          have chosen := (mate_some owner active matching (owner edge) edge).mpr ⟨selected, rfl⟩
          simp [exchange, selected, chosen]

def pairing (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Equiv.Perm (Fin q ⊕ Fin e) where
  toFun := exchange owner active
  invFun := exchange owner active
  left_inv := exchange_involutive owner active matching
  right_inv := exchange_involutive owner active matching

def permutation (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Equiv.Perm (Fin (q + e)) :=
  finSumFinEquiv.symm.trans ((pairing owner active matching).trans finSumFinEquiv)

theorem permutation_apply (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (port : Fin (q + e)) :
    permutation owner active matching port =
      finSumFinEquiv (exchange owner active (finSumFinEquiv.symm port)) := rfl

theorem permutation_involutive (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Function.Involutive (permutation owner active matching) := by
  intro port
  simp only [permutation_apply, Equiv.symm_apply_apply]
  rw [exchange_involutive owner active matching (finSumFinEquiv.symm port)]
  exact finSumFinEquiv.apply_symm_apply port







open Counter.Reversible

/-- The guard class depends only on a static source instruction. -/
def actionGuard : Action 2 → ReversibleControl.Guard
  | .shift _ _ => none
  | .test register atZero => some (register, atZero)

theorem compatible_guards_ne {first second : Action 2}
    (compatible : first.Compatible second) : actionGuard first ≠ actionGuard second := by
  cases first <;> cases second <;> simp only [Action.Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  simpa only [actionGuard, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and] using different



/-- Static selection of one of the five possible guard classes. -/
def selected (table : Table 2 q e) (guard : ReversibleControl.Guard) (edge : Fin e) : Bool :=
  decide (actionGuard (table edge).action = guard)

@[simp] theorem selected_iff (table : Table 2 q e) (guard : ReversibleControl.Guard)
    (edge : Fin e) : selected table guard edge = true ↔ actionGuard (table edge).action = guard := by
  simp [selected]

theorem sourceMatching (table : Table 2 q e) (deterministic : Deterministic table)
    (guard : ReversibleControl.Guard) :
    Matching (fun edge => (table edge).source) (selected table guard) := by
  intro first second fs ss same_source
  by_contra different
  exact compatible_guards_ne (deterministic first second different same_source)
    (((selected_iff table guard first).mp fs).trans ((selected_iff table guard second).mp ss).symm)

theorem targetMatching (table : Table 2 q e) (compatible : TargetCompatible table)
    (guard : ReversibleControl.Guard) :
    Matching (fun edge => (table edge).target) (selected table guard) := by
  intro first second fs ss same_target
  by_contra different
  exact compatible_guards_ne (compatible first second different same_target)
    (((selected_iff table guard first).mp fs).trans ((selected_iff table guard second).mp ss).symm)

/-- These are all guard classes; the list is independent of the compiled table. -/
def guards : List ReversibleControl.Guard :=
  [none, some (0, true), some (0, false), some (1, true), some (1, false)]





end Monodromy.ReversiblePorts

/-!
## Native guarded routing
-/

namespace Monodromy.ReversibleRouting

open CoupledContinuation Counter.Reversible ReversiblePorts

variable {q e : ℕ} [NeZero (q + e)]

/-- Alternatives attached to a common owner are complementary unchanged tests. -/
def CompatibleOwner (table : Table 2 q e) (owner : Fin e → Fin q) : Prop :=
  ∀ first second, first ≠ second → owner first = owner second →
    Action.Compatible (table first).action (table second).action

variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))

/-- This stage contains only a fixed guard and its static finite port permutation. -/
def route (guard : ReversibleControl.Guard) : Program (q + e) :=
  ReversibleControl.program guard (permutation owner (selected table guard) (matching guard))

/-- Head-first execution of actual native return maps. -/
noncomputable def run (stages : List ReversibleControl.Guard) (state : Memory) : Memory :=
  stages.foldl (fun current guard => (route table owner matching guard).advance current) state

@[simp] theorem run_nil (state : Memory) : run table owner matching [] state = state := rfl



/-- Only the finite address is abbreviated; the retained state is the same three roots. -/
noncomputable def point (values : Fin 2 → ℤ) (index : Fin (q + e)) : Memory :=
  prepare (values 0) (values 1) (index.val : ℤ)





/-- The same actual native route reverses itself on the entire state fiber. -/
theorem route_involutive (guard : ReversibleControl.Guard) :
    Function.Involutive (route table owner matching guard).advance := by
  let pairing := permutation owner (selected table guard) (matching guard)
  have symmetry : pairing.symm = pairing := by
    apply Equiv.ext
    intro index
    apply pairing.injective
    calc
      pairing (pairing.symm index) = index := pairing.apply_symm_apply index
      _ = pairing (pairing index) :=
        (permutation_involutive owner (selected table guard) (matching guard) index).symm
  intro state
  change (ReversibleControl.program guard pairing).advance
    ((ReversibleControl.program guard pairing).advance state) = state
  simpa only [symmetry] using ReversibleControl.inverse guard pairing state













end Monodromy.ReversibleRouting

/-!
## The fixed reversible native compiler
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation ReversiblePorts

variable {q e : ℕ} [NeZero q]

instance : NeZero (q + e) := ⟨by have := NeZero.ne q; omega⟩

/-- A finite source instruction fixes a signed displacement before execution. -/
def displacement : Action 2 → ℤ × ℤ
  | .shift register amount => if register = 0 then (amount, 0) else (0, amount)
  | .test _ _ => (0, 0)





/-- Source vertices and edge ports are finite addresses in the same control root. -/
def point (address : Fin (q + e)) (values : Fin 2 → ℤ) : Memory :=
  prepare (values 0) (values 1) address.val

def sourcePoint (state : State 2 q) : Memory :=
  point (Fin.castAdd e state.1) state.2

def portPoint (edge : Fin e) (values : Fin 2 → ℤ) : Memory :=
  point (Fin.natAdd q edge) values



/-- Program data specifies the displacement at each finite edge port. -/
def moves (table : Table 2 q e) (address : Fin (q + e)) : ℤ × ℤ :=
  match finSumFinEquiv.symm address with
  | .inl _ => (0, 0)
  | .inr edge => displacement (table edge).action

def update (table : Table 2 q e) : Program (q + e) := ReversibleMemory.program (moves table)





def sourceLayers (table : Table 2 q e) (deterministic : Deterministic table) :
    List (Program (q + e)) :=
  guards.map (ReversibleRouting.route table (fun edge => (table edge).source)
    (sourceMatching table deterministic))

def targetLayers (table : Table 2 q e) (compatible : TargetCompatible table) :
    List (Program (q + e)) :=
  guards.reverse.map (ReversibleRouting.route table (fun edge => (table edge).target)
    (targetMatching table compatible))

/-- Five outward matchings, one memory update, and five reverse inward matchings. -/
def layers (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : List (Program (q + e)) :=
  sourceLayers table deterministic ++ update table :: targetLayers table compatible

omit [NeZero q] in
theorem layers_length (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : (layers table deterministic compatible).length = 11 := by
  simp [layers, sourceLayers, targetLayers, guards]







/-- Finite stages are packed into the existing upper branch, with eleven fixed clock phases. -/
def stages (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) : Program (q + e) :=
  (layers table deterministic compatible).get
    ⟨phase.val, by rw [layers_length]; exact phase.isLt⟩



def program (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Program (11 * (q + e)) :=
  StagedProgram.compile 11 (q + e) (stages table deterministic compatible)

def iota (state : State 2 q) : Memory := StagedProgram.embed 11 0 (sourcePoint (e := e) state)







/-- The only non-involutive layer is undone by the negated static memory displacement. -/
def backwardStages (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) : Program (q + e) :=
  if phase = 5 then ReversibleMemory.program (ReversibleMemory.negate (moves table))
  else stages table deterministic compatible phase

omit [NeZero q] in
theorem stages_update (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : stages table deterministic compatible 5 = update table := rfl

theorem stages_involutive (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) (different : phase ≠ 5) :
    Function.Involutive (stages table deterministic compatible phase).advance := by
  fin_cases phase <;> first
    | exact (different rfl).elim
    | exact ReversibleRouting.route_involutive _ _ _ _

theorem backward_left (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) (state : Memory) :
    (backwardStages table deterministic compatible phase).advance
      ((stages table deterministic compatible phase).advance state) = state := by
  by_cases middle : phase = 5
  · subst phase
    rw [backwardStages, ite_eq_left rfl, stages_update]
    exact ReversibleMemory.inverse (moves table) state
  · rw [backwardStages, ite_eq_right middle]
    exact stages_involutive table deterministic compatible phase middle state

theorem backward_right (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) (state : Memory) :
    (stages table deterministic compatible phase).advance
      ((backwardStages table deterministic compatible phase).advance state) = state := by
  by_cases middle : phase = 5
  · subst phase
    rw [backwardStages, ite_eq_left rfl, stages_update]
    simpa only [update, ReversibleMemory.negate_negate] using
      ReversibleMemory.inverse (ReversibleMemory.negate (moves table)) state
  · rw [backwardStages, ite_eq_right middle]
    exact stages_involutive table deterministic compatible phase middle state

/-- Reverse execution is another fixed native word table, selected from returned roots. -/
def reverseProgram (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Program (11 * (q + e)) :=
  StagedProgram.compileReverse 11 (q + e) (backwardStages table deterministic compatible)

theorem reverse_after_forward (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : Memory) :
    (reverseProgram table deterministic compatible).advance
      ((program table deterministic compatible).advance state) = state :=
  StagedProgram.left_inverse 11 (q + e) _ _
    (backward_left table deterministic compatible) state

theorem forward_after_reverse (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : Memory) :
    (program table deterministic compatible).advance
      ((reverseProgram table deterministic compatible).advance state) = state :=
  StagedProgram.right_inverse 11 (q + e) _ _
    (backward_right table deterministic compatible) state

/-- Both directions are fixed native tables on the same retained fiber. -/
def executionEquiv (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Memory ≃ Memory where
  toFun := (program table deterministic compatible).advance
  invFun := (reverseProgram table deterministic compatible).advance
  left_inv := reverse_after_forward table deterministic compatible
  right_inv := forward_after_reverse table deterministic compatible





end Monodromy.ReversibleCompilation

/-!
## Complete execution and actual lifted results
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]

/-- This finite bit table examines only static source edges, never current register values. -/
def haltMark (table : Table 2 q e) (address : Fin (q + e)) : Bool :=
  match finSumFinEquiv.symm address with
  | .inl position => decide (¬ ∃ edge, (table edge).source = position)
  | .inr _ => false





/-- Only stopping bits change; the entire fixed geometric word table is retained. -/
def haltingProgram (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Program (11 * (q + e)) :=
  StagedProgram.markedCompile 11 (q + e) (stages table deterministic compatible) (haltMark table)











































end Monodromy.ReversibleCompilation

/-!
## Protected source register relocation
-/

namespace Monodromy.Counter.Reversible.RegisterRelocation

variable {n m q e : ℕ}

def mapAction (register : Fin n → Fin m) : Action n → Action m
  | .shift index amount => .shift (register index) amount
  | .test index atZero => .test (register index) atZero



def mapTable (register : Fin n → Fin m) (source : Table n q e) : Table m q e :=
  fun edge => ⟨(source edge).source, (source edge).target, mapAction register (source edge).action⟩

theorem compatible_iff (register : Fin n → Fin m) (faithful : Function.Injective register)
    (first second : Action n) :
    Action.Compatible (mapAction register first) (mapAction register second) ↔
      Action.Compatible first second := by
  cases first <;> cases second <;> simp [mapAction, Action.Compatible, faithful.eq_iff]

theorem deterministic (register : Fin n → Fin m) (faithful : Function.Injective register)
    (source : Table n q e) (valid : Deterministic source) :
    Deterministic (mapTable register source) := by
  intro first second different same
  exact (compatible_iff register faithful _ _).mpr (valid first second different same)

theorem targetCompatible (register : Fin n → Fin m) (faithful : Function.Injective register)
    (source : Table n q e) (valid : TargetCompatible source) :
    TargetCompatible (mapTable register source) := by
  intro first second different same
  exact (compatible_iff register faithful _ _).mpr (valid first second different same)







/-- Only the selected source registers are inserted into the protected background. -/
def embed (register : Fin n → Fin m) (background : Fin m → ℤ) (state : State n q) : State m q :=
  (state.1, Function.extend register state.2 background)



















end Monodromy.Counter.Reversible.RegisterRelocation

/-!
## Composition by gluing control interfaces
-/

namespace Monodromy.Counter.Reversible.Glue

variable {n q₁ q₂ e₁ e₂ : ℕ}

def leftControl (exit : Fin (q₁ + 1)) (entry : Fin q₂) : Fin (q₁ + 1) → Fin (q₁ + q₂) :=
  Fin.insertNth exit (Fin.natAdd q₁ entry) (Fin.castAdd q₂)

def rightControl (position : Fin q₂) : Fin (q₁ + q₂) := Fin.natAdd q₁ position











def mapEdge {q k : ℕ} (control : Fin q → Fin k) (edge : Edge n q) : Edge n k :=
  ⟨control edge.source, control edge.target, edge.action⟩

def mapState {q k : ℕ} (control : Fin q → Fin k) (state : State n q) : State n k :=
  (control state.1, state.2)

def table (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂) : Table n (q₁ + q₂) (e₁ + e₂) :=
  fun index => match finSumFinEquiv.symm index with
    | .inl edge => mapEdge (leftControl exit entry) (first edge)
    | .inr edge => mapEdge rightControl (second edge)





















/-! Finite traces inside larger control graphs. -/

section FiniteTrace

variable {n m q k e f : ℕ}







end FiniteTrace

end Monodromy.Counter.Reversible.Glue

/-!
## Finite port identification

A partial matching identifies existing output and input positions. Original
edges and actions are retained, including in cyclic networks.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PortNetwork

variable {n q e : ℕ}

/-- A partial injective matching from exits with no outgoing edge to entries
with no incoming edge. Destinations are not themselves matched exits. -/
structure Wiring (original : Table n q e) where
  link : Fin q → Option (Fin q)
  terminal : ∀ {exit entry}, link exit = some entry → link entry = none
  injective : ∀ {first second entry}, link first = some entry →
    link second = some entry → first = second
  source_free : ∀ index, link (original index).source = none
  target_free : ∀ index exit, link exit ≠ some (original index).target

variable {original : Table n q e} (wiring : Wiring original)

/-- Matched exits disappear; their incident targets use the selected entry. -/
abbrev Node := {position : Fin q // wiring.link position = none}

def representative (position : Fin q) : Node wiring :=
  match selected : wiring.link position with
  | none => ⟨position, selected⟩
  | some entry => ⟨entry, wiring.terminal selected⟩

def size : ℕ := Fintype.card (Node wiring)

def nodeEquiv : Node wiring ≃ Fin (size wiring) := Fintype.equivFin _

def control (position : Fin q) : Fin (size wiring) :=
  nodeEquiv wiring (representative wiring position)

def table : Table n (size wiring) e := fun index =>
  Glue.mapEdge (control wiring) (original index)







@[simp] theorem representative_unlinked (position : Fin q)
    (unlinked : wiring.link position = none) :
    (representative wiring position).val = position := by
  unfold representative
  split <;> simp_all

@[simp] theorem representative_linked (exit entry : Fin q)
    (linked : wiring.link exit = some entry) :
    (representative wiring exit).val = entry := by
  unfold representative
  split <;> simp_all





theorem control_unlinked_injective {first second : Fin q}
    (first_free : wiring.link first = none) (second_free : wiring.link second = none)
    (same : control wiring first = control wiring second) : first = second := by
  have representatives := (nodeEquiv wiring).injective same
  have positions := congrArg Subtype.val representatives
  simpa only [representative_unlinked wiring first first_free,
    representative_unlinked wiring second second_free] using positions

/-- Sources are never normalized, so their incidence is preserved exactly. -/
theorem source_eq_iff (first second : Fin e) :
    control wiring (original first).source = control wiring (original second).source ↔
      (original first).source = (original second).source := by
  constructor
  · exact control_unlinked_injective wiring (wiring.source_free first) (wiring.source_free second)
  · exact congrArg (control wiring)

/-- Distinct original targets cannot merge: matched entries have no incoming edge,
and the exit-to-entry wiring is injective. -/
theorem target_eq_iff (first second : Fin e) :
    control wiring (original first).target = control wiring (original second).target ↔
      (original first).target = (original second).target := by
  constructor
  · intro same
    have positions := congrArg Subtype.val ((nodeEquiv wiring).injective same)
    cases left : wiring.link (original first).target with
    | none =>
      cases right : wiring.link (original second).target with
      | none => exact control_unlinked_injective wiring left right same
      | some entry =>
        have eq_entry : (original first).target = entry := by
          simpa only [representative_unlinked wiring _ left,
            representative_linked wiring _ _ right] using positions
        exact False.elim (wiring.target_free first (original second).target (eq_entry ▸ right))
    | some entry =>
      cases right : wiring.link (original second).target with
      | none =>
        have eq_entry : entry = (original second).target := by
          simpa only [representative_linked wiring _ _ left,
            representative_unlinked wiring _ right] using positions
        exact False.elim (wiring.target_free second (original first).target (eq_entry ▸ left))
      | some other =>
        have entries : entry = other := by
          simpa only [representative_linked wiring _ _ left,
            representative_linked wiring _ _ right] using positions
        exact wiring.injective left (entries ▸ right)
  · exact congrArg (control wiring)

/-- Gluing preserves the original forward local reversibility condition. -/
theorem deterministic (valid : Deterministic original) : Deterministic (table wiring) := by
  intro first second different same
  exact valid first second different ((source_eq_iff wiring first second).mp same)

/-- Gluing preserves the original backward local reversibility condition. -/
theorem targetCompatible (valid : TargetCompatible original) : TargetCompatible (table wiring) := by
  intro first second different same
  exact valid first second different ((target_eq_iff wiring first second).mp same)







/-- Bounded selection of an entry from a finite, functional port relation. -/
def relationLink (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (exit : Fin q) : Option (Fin q) :=
  if connected : ∃ entry, connection exit entry then
    some (Fin.find (connection exit) connected)
  else none

theorem relationLink_some_iff (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (functional : ∀ {exit first second}, connection exit first →
      connection exit second → first = second) (exit entry : Fin q) :
    relationLink connection exit = some entry ↔ connection exit entry := by
  unfold relationLink
  split_ifs with connected
  · rw [Option.some.injEq]
    constructor
    · intro same
      rw [← same]
      exact Fin.find_spec connected
    · intro actual
      exact functional (Fin.find_spec connected) actual
  · constructor
    · intro impossible
      cases impossible
    · intro actual
      exact False.elim (connected ⟨entry, actual⟩)

theorem relationLink_none_iff (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (exit : Fin q) :
    relationLink connection exit = none ↔ ∀ entry, ¬ connection exit entry := by
  unfold relationLink
  split_ifs with connected
  · constructor
    · intro impossible
      cases impossible
    · intro absent
      exact False.elim (absent _ (Fin.find_spec connected))
  · exact ⟨fun _ entry actual => connected ⟨entry, actual⟩, fun _ => rfl⟩

/-- A partial matching of existing exits and entries supplies static wiring. -/
def Wiring.ofRelation (original : Table n q e)
    (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (functional : ∀ {exit first second}, connection exit first →
      connection exit second → first = second)
    (backward : ∀ {first second entry}, connection first entry →
      connection second entry → first = second)
    (terminal : ∀ {exit entry}, connection exit entry → ∀ next, ¬ connection entry next)
    (source_free : ∀ index entry, ¬ connection (original index).source entry)
    (target_free : ∀ index exit, ¬ connection exit (original index).target) :
    Wiring original where
  link := relationLink connection
  terminal := fun linked => (relationLink_none_iff connection _).mpr
    (terminal ((relationLink_some_iff connection functional _ _).mp linked))
  injective := fun first second => backward
    ((relationLink_some_iff connection functional _ _).mp first)
    ((relationLink_some_iff connection functional _ _).mp second)
  source_free := fun index => (relationLink_none_iff connection _).mpr (source_free index)
  target_free := fun index exit linked => target_free index exit
    ((relationLink_some_iff connection functional _ _).mp linked)

end Monodromy.Counter.Reversible.PortNetwork

end


/-!
## One reversible radix graph: unpacking and packing
-/

namespace Monodromy.Counter.Reversible.Radix

variable (p : ℕ) [NeZero p]

def size : ℕ := 3 + p * 8
def edges : ℕ := 3 + p * 9

abbrev Node := Fin 3 ⊕ (Fin p × Fin 8)
abbrev Arc := Fin 3 ⊕ (Fin p × Fin 9)

def nodeEquiv : Node p ≃ Fin (size p) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def arcEquiv : Arc p ≃ Fin (edges p) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def global (position : Fin 3) : Fin (size p) := nodeEquiv p (.inl position)
def block (remainder : Fin p) (phase : Fin 8) : Fin (size p) :=
  nodeEquiv p (.inr (remainder, phase))

def entry : Fin (size p) := global p 0
def finish (remainder : Fin p) : Fin (size p) := block p remainder 7

/-- A full block increments the quotient before returning to remainder zero. -/
def next (remainder : Fin p) : Node p :=
  if bound : remainder.val + 1 < p then .inr (⟨remainder.val + 1, bound⟩, 0)
  else .inl 1

omit [NeZero p] in
@[simp] theorem next_eq_block (remainder other : Fin p) (phase : Fin 8) :
    next p remainder = Sum.inr (other, phase) ↔
      remainder.val + 1 = other.val ∧ phase = 0 := by
  unfold next
  split_ifs with bound
  · simp only [Sum.inr.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨same, phase_eq⟩
      exact ⟨congrArg Fin.val same, phase_eq.symm⟩
    · rintro ⟨same, phase_eq⟩
      exact ⟨Fin.ext same, phase_eq.symm⟩
  · constructor
    · intro impossible
      cases impossible
    · rintro ⟨same, _⟩
      exact (bound (same ▸ other.isLt)).elim

omit [NeZero p] in
@[simp] theorem next_eq_global (remainder : Fin p) (position : Fin 3) :
    next p remainder = Sum.inl position ↔ position = 1 ∧ remainder.val + 1 = p := by
  unfold next
  split_ifs with bound
  · constructor
    · intro impossible
      cases impossible
    · rintro ⟨_, same⟩
      omega
  · simp only [Sum.inl.injEq]
    have last : remainder.val + 1 = p := by have := remainder.isLt; omega
    simp [last, eq_comm]

omit [NeZero p] in
theorem next_injective : Function.Injective (next p) := by
  intro first second same
  unfold next at same
  split_ifs at same <;> try cases same
  · have values := congrArg (fun node : Node p => node.elim (fun _ => 0) (fun pair => pair.1.val)) same
    apply Fin.ext
    dsimp at values
    omega
  · apply Fin.ext
    have := first.isLt
    have := second.isLt
    omega

omit [NeZero p] in
@[simp] theorem next_eq_next (first second : Fin p) : next p first = next p second ↔ first = second :=
  (next_injective p).eq_iff

/-- Only finite control data and unit shifts occur in the edge descriptions. -/
def origin : Arc p → Node p
  | .inl position => .inl position
  | .inr (remainder, edge) =>
      ![Sum.inr (remainder, 0), Sum.inr (remainder, 0), Sum.inr (remainder, 1),
        Sum.inr (remainder, 2), Sum.inr (remainder, 3), Sum.inr (remainder, 3),
        Sum.inr (remainder, 4), Sum.inr (remainder, 5), Sum.inr (remainder, 6)] edge

def destination : Arc p → Node p
  | .inl position => ![Sum.inr (0, 0), Sum.inl 2, Sum.inr (0, 0)] position
  | .inr (remainder, edge) =>
      ![Sum.inr (remainder, 2), Sum.inr (remainder, 1), next p remainder,
        Sum.inr (remainder, 3), Sum.inr (remainder, 7), Sum.inr (remainder, 4),
        Sum.inr (remainder, 5), Sum.inr (remainder, 6), Sum.inr (remainder, 3)] edge

def operation : Arc p → Action 2
  | .inl position => ![Action.test 1 true, Action.shift 1 1, Action.test 1 false] position
  | .inr (_, edge) =>
      ![Action.test 0 true, Action.test 0 false, Action.shift 0 (-1),
        Action.test 0 true, Action.test 1 true, Action.test 1 false,
        Action.shift 1 (-1), Action.shift 0 1, Action.test 0 false] edge

def table : Table 2 (size p) (edges p) := fun index =>
  let arc := (arcEquiv p).symm index
  ⟨nodeEquiv p (origin p arc), nodeEquiv p (destination p arc), operation p arc⟩

@[simp] theorem table_arc (arc : Arc p) :
    table p (arcEquiv p arc) =
      ⟨nodeEquiv p (origin p arc), nodeEquiv p (destination p arc), operation p arc⟩ := by
  simp [table]



theorem deterministic : Deterministic (table p) := by
  intro first second different same_source
  obtain ⟨first, rfl⟩ := (arcEquiv p).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv p).surjective second
  have distinct : first ≠ second := fun same => different (congrArg (arcEquiv p) same)
  have same : origin p first = origin p second := (nodeEquiv p).injective (by simpa using same_source)
  clear different same_source
  simp only [table_arc]
  change Action.Compatible (operation p first) (operation p second)
  rcases first with first | ⟨r, first⟩ <;>
    rcases second with second | ⟨s, second⟩ <;>
    fin_cases first <;> fin_cases second <;>
    simp_all [origin, operation, Action.Compatible]

theorem targetCompatible : TargetCompatible (table p) := by
  intro first second different same_target
  obtain ⟨first, rfl⟩ := (arcEquiv p).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv p).surjective second
  have distinct : first ≠ second := fun same => different (congrArg (arcEquiv p) same)
  have same : destination p first = destination p second :=
    (nodeEquiv p).injective (by simpa using same_target)
  clear different same_target
  simp only [table_arc]
  change Action.Compatible (operation p first) (operation p second)
  rcases first with first | ⟨r, first⟩ <;>
    rcases second with second | ⟨s, second⟩ <;>
    fin_cases first <;> fin_cases second <;>
    simp_all [destination, operation, Action.Compatible]
  all_goals
    have reversed := same.symm
    simp at reversed

def point (position : Fin (size p)) (left right : ℤ) : State 2 (size p) :=
  (position, ![left, right])


instance : NeZero (size p) := ⟨by simp [size]⟩

/-- The finite port determines the conditions required by singleton tests and decrements. -/
def admissible : Node p → ℤ → ℤ → Prop
  | .inl position, _, right => ![right = 0, True, right ≠ 0] position
  | .inr (_, phase), left, right =>
      ![True, 0 < left, left = 0, True, 0 < right, True, left ≠ 0, True] phase

def Valid (state : State 2 (size p)) : Prop :=
  0 ≤ state.2 0 ∧ 0 ≤ state.2 1 ∧
    admissible p ((nodeEquiv p).symm state.1) (state.2 0) (state.2 1)









omit [NeZero p] in
theorem origin_ne_finish (arc : Arc p) (remainder : Fin p) :
    origin p arc ≠ Sum.inr (remainder, (7 : Fin 8)) := by
  rcases arc with position | ⟨other, index⟩
  · simp [origin]
  · fin_cases index <;> simp [origin]

theorem no_outgoing_finish (remainder : Fin p) :
    ¬ ∃ index, (table p index).source = finish p remainder := by
  rintro ⟨index, source⟩
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  have same : origin p arc = Sum.inr (remainder, (7 : Fin 8)) := by
    apply (nodeEquiv p).injective
    simpa only [table_arc, finish, block] using source
  exact origin_ne_finish p arc remainder same































/-- The original entry has no incoming edge, so the reversed graph stops there. -/
theorem no_incoming_entry (index : Fin (edges p)) : (table p index).target ≠ entry p := by
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  intro incoming
  have same : destination p arc = Sum.inl (0 : Fin 3) := by
    apply (nodeEquiv p).injective
    simpa only [table_arc, entry, global] using incoming
  rcases arc with index | ⟨remainder, index⟩ <;> fin_cases index <;> simp [destination] at same





end Monodromy.Counter.Reversible.Radix

/-!
## Read-only remainder observation by identified radix ports
-/

noncomputable section

namespace Monodromy.Counter.Reversible.RadixObservation

variable (p m : ℕ) [NeZero p]

abbrev RawNode := (Fin 2 × Fin m) × Fin (Radix.size p)
abbrev RawArc := (Fin 2 × Fin m) × Fin (Radix.edges p)

def rawSize : ℕ := (2 * m) * Radix.size p
def edges : ℕ := (2 * m) * Radix.edges p

def rawNodeEquiv : RawNode p m ≃ Fin (rawSize p m) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def arcEquiv : RawArc p m ≃ Fin (edges p m) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def rawControl (direction : Fin 2) (row : Fin m) (position : Fin (Radix.size p)) :
    Fin (rawSize p m) := rawNodeEquiv p m ((direction, row), position)

def component (direction : Fin 2) : Table 2 (Radix.size p) (Radix.edges p) :=
  if direction = 0 then Radix.table p else reverseTable (Radix.table p)

 theorem component_deterministic (direction : Fin 2) : Deterministic (component p direction) := by
  unfold component
  split_ifs
  · exact Radix.deterministic p
  · exact reverseTable_deterministic _ (Radix.targetCompatible p)

 theorem component_targetCompatible (direction : Fin 2) :
    TargetCompatible (component p direction) := by
  unfold component
  split_ifs
  · exact Radix.targetCompatible p
  · exact reverseTable_targetCompatible _ (Radix.deterministic p)

def rawTable : Table 2 (rawSize p m) (edges p m) := fun index =>
  let arc := (arcEquiv p m).symm index
  Glue.mapEdge (rawControl p m arc.1.1 arc.1.2) (component p arc.1.1 arc.2)

@[simp] theorem rawTable_arc (owner : Fin 2 × Fin m) (index : Fin (Radix.edges p)) :
    rawTable p m (arcEquiv p m (owner, index)) =
      Glue.mapEdge (rawControl p m owner.1 owner.2) (component p owner.1 index) := by
  simp only [rawTable, Equiv.symm_apply_apply]

omit [NeZero p] in
 theorem rawControl_eq_iff (first second : Fin 2 × Fin m)
    (initial final : Fin (Radix.size p)) :
    rawControl p m first.1 first.2 initial = rawControl p m second.1 second.2 final ↔
      first = second ∧ initial = final := by
  change rawNodeEquiv p m (first, initial) = rawNodeEquiv p m (second, final) ↔ _
  rw [(rawNodeEquiv p m).injective.eq_iff, Prod.mk.injEq]

 theorem raw_deterministic : Deterministic (rawTable p m) := by
  intro first second different same
  obtain ⟨⟨owner, first⟩, rfl⟩ := (arcEquiv p m).surjective first
  obtain ⟨⟨other, second⟩, rfl⟩ := (arcEquiv p m).surjective second
  simp only [rawTable_arc, Glue.mapEdge] at same ⊢
  have ports := (rawControl_eq_iff p m owner other _ _).mp same
  rcases ports with ⟨rfl, positions⟩
  exact component_deterministic p owner.1 first second
    (fun equal => different (by subst second; rfl)) positions

 theorem raw_targetCompatible : TargetCompatible (rawTable p m) := by
  intro first second different same
  obtain ⟨⟨owner, first⟩, rfl⟩ := (arcEquiv p m).surjective first
  obtain ⟨⟨other, second⟩, rfl⟩ := (arcEquiv p m).surjective second
  simp only [rawTable_arc, Glue.mapEdge] at same ⊢
  have ports := (rawControl_eq_iff p m owner other _ _).mp same
  rcases ports with ⟨rfl, positions⟩
  exact component_targetCompatible p owner.1 first second
    (fun equal => different (by subst second; rfl)) positions

/-- A finite node address exposes whether it is a radix finish port. -/
def finishQuery (position : Fin (Radix.size p)) : Option (Fin p) :=
  match (Radix.nodeEquiv p).symm position with
  | .inl _ => none
  | .inr (remainder, phase) => if phase = 7 then some remainder else none



omit [NeZero p] in
theorem finishQuery_some {position : Fin (Radix.size p)} {remainder : Fin p}
    (selected : finishQuery p position = some remainder) : position = Radix.finish p remainder := by
  unfold finishQuery at selected
  cases shape : (Radix.nodeEquiv p).symm position with
  | inl global => simp [shape] at selected
  | inr pair =>
    rcases pair with ⟨symbol, phase⟩
    rw [shape] at selected
    dsimp only at selected
    split_ifs at selected with last
    · have symbols := Option.some.inj selected
      subst symbol
      apply (Radix.nodeEquiv p).symm.injective
      simp only [Radix.finish, Radix.block, Equiv.symm_apply_apply, shape, last]

 theorem finishQuery_source (index : Fin (Radix.edges p)) :
    finishQuery p (Radix.table p index).source = none := by
  cases selected : finishQuery p (Radix.table p index).source with
  | none => rfl
  | some remainder =>
    exact (Radix.no_outgoing_finish p remainder ⟨index, finishQuery_some p selected⟩).elim

/-- Only forward finish ports are matched, directly to the corresponding reversed copy. -/
def link (permutation : Fin p → Equiv.Perm (Fin m)) (position : Fin (rawSize p m)) :
    Option (Fin (rawSize p m)) :=
  let node := (rawNodeEquiv p m).symm position
  if node.1.1 = 0 then
    (finishQuery p node.2).map fun remainder => rawControl p m 1 (permutation remainder node.1.2) node.2
  else none

omit [NeZero p] in
@[simp] theorem link_backward (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (position : Fin (Radix.size p)) :
    link p m permutation (rawControl p m 1 row position) = none := by
  simp [link, rawControl]



omit [NeZero p] in
/-- Every link is a finish-port equality; its remainder is an address in a fixed finite table. -/
theorem link_some (permutation : Fin p → Equiv.Perm (Fin m))
    {exit entry : Fin (rawSize p m)} (linked : link p m permutation exit = some entry) :
    ∃ row remainder, exit = rawControl p m 0 row (Radix.finish p remainder) ∧
      entry = rawControl p m 1 (permutation remainder row) (Radix.finish p remainder) := by
  obtain ⟨⟨⟨direction, row⟩, position⟩, rfl⟩ := (rawNodeEquiv p m).surjective exit
  change link p m permutation (rawControl p m direction row position) = some entry at linked
  simp only [link, rawControl, Equiv.symm_apply_apply] at linked
  split_ifs at linked with forward
  · cases selected : finishQuery p position with
    | none => simp [selected] at linked
    | some remainder =>
      simp only [selected, Option.map_some] at linked
      have target : rawControl p m 1 (permutation remainder row) position = entry :=
        Option.some.inj linked
      have position_eq := finishQuery_some p selected
      exact ⟨row, remainder, by simp only [forward, position_eq, rawControl],
        by simpa only [position_eq] using target.symm⟩

/-- Finite wiring is the only new data; the two existing edge families are unchanged. -/
def wiring (permutation : Fin p → Equiv.Perm (Fin m)) : PortNetwork.Wiring (rawTable p m) where
  link := link p m permutation
  terminal := by
    intro exit entry linked
    obtain ⟨row, remainder, rfl, rfl⟩ := link_some p m permutation linked
    exact link_backward p m permutation _ _
  injective := by
    intro first second entry left right
    obtain ⟨row, remainder, rfl, equal_left⟩ := link_some p m permutation left
    obtain ⟨other, symbol, rfl, equal_right⟩ := link_some p m permutation right
    have ports := (rawControl_eq_iff p m (1, permutation remainder row)
      (1, permutation symbol other) _ _).mp (equal_left.symm.trans equal_right)
    have symbols : remainder = symbol := by
      apply Fin.ext
      have raw := (Radix.nodeEquiv p).injective ports.2
      exact congrArg (fun node : Radix.Node p => node.elim (fun _ => 0) (fun pair => pair.1.val)) raw
    subst symbol
    have rows := (permutation remainder).injective (congrArg Prod.snd ports.1)
    rw [rows]
  source_free := by
    intro index
    obtain ⟨⟨⟨direction, row⟩, index⟩, rfl⟩ := (arcEquiv p m).surjective index
    fin_cases direction <;> simp [rawTable_arc, Glue.mapEdge, component, link, rawControl, finishQuery_source]
  target_free := by
    intro index exit linked
    obtain ⟨row, remainder, _, equal⟩ := link_some p m permutation linked
    obtain ⟨⟨⟨direction, other⟩, index⟩, rfl⟩ := (arcEquiv p m).surjective index
    fin_cases direction
    · simp only [rawTable_arc, Glue.mapEdge] at equal
      change rawControl p m 0 other (Radix.table p index).target =
        rawControl p m 1 (permutation remainder row) (Radix.finish p remainder) at equal
      have impossible : ((0 : Fin 2), other) = (1, permutation remainder row) :=
        ((rawControl_eq_iff p m (0, other) (1, permutation remainder row) _ _).mp equal).1
      exact (by simpa using congrArg Prod.fst impossible)
    · simp only [rawTable_arc, Glue.mapEdge] at equal
      change rawControl p m 1 other (Radix.table p index).source =
        rawControl p m 1 (permutation remainder row) (Radix.finish p remainder) at equal
      have ports := (rawControl_eq_iff p m (1, other) (1, permutation remainder row) _ _).mp equal
      exact Radix.no_outgoing_finish p remainder ⟨index, ports.2⟩

def size (permutation : Fin p → Equiv.Perm (Fin m)) : ℕ := PortNetwork.size (wiring p m permutation)

def table (permutation : Fin p → Equiv.Perm (Fin m)) : Table 2 (size p m permutation) (edges p m) :=
  PortNetwork.table (wiring p m permutation)

def front (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m)
    (position : Fin (Radix.size p)) : Fin (size p m permutation) :=
  PortNetwork.control (wiring p m permutation) (rawControl p m 0 row position)

def back (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m)
    (position : Fin (Radix.size p)) : Fin (size p m permutation) :=
  PortNetwork.control (wiring p m permutation) (rawControl p m 1 row position)

theorem deterministic (permutation : Fin p → Equiv.Perm (Fin m)) : Deterministic (table p m permutation) :=
  PortNetwork.deterministic _ (raw_deterministic p m)

theorem targetCompatible (permutation : Fin p → Equiv.Perm (Fin m)) : TargetCompatible (table p m permutation) :=
  PortNetwork.targetCompatible _ (raw_targetCompatible p m)







def inputPort (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) :
    Fin (size p m permutation) := front p m permutation row (Radix.entry p)

def outputPort (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) :
    Fin (size p m permutation) := back p m permutation row (Radix.entry p)

def point (permutation : Fin p → Equiv.Perm (Fin m)) (position : Fin (size p m permutation))
    (left right : ℤ) : State 2 (size p m permutation) := (position, ![left, right])

instance [NeZero m] (permutation : Fin p → Equiv.Perm (Fin m)) : NeZero (size p m permutation) := by
  change NeZero (Fintype.card (PortNetwork.Node (wiring p m permutation)))
  exact ⟨Nat.ne_of_gt (Fintype.card_pos_iff.mpr
    ⟨PortNetwork.representative (wiring p m permutation) (rawControl p m 1 0 (Radix.entry p))⟩)⟩











end Monodromy.Counter.Reversible.RadixObservation

end


/-!
## A source specification for reversible transition recording
-/

namespace Monodromy.Counter.Recorded

variable {n m : ℕ}

/-- One nonzero radix digit records a finite transition tag. -/
def push {k : ℕ} (symbol : Fin k) (history : ℕ) : ℕ :=
  (k + 1) * history + symbol.val + 1







/-- The tag retains the old address and the zero/nonzero branch of a decrement. -/
def branch (program : Program n m) (state : Configuration n m) : Fin 2 :=
  match program state.pc with
  | .dec register _ _ => if state.counters register = 0 then 0 else 1
  | _ => 0

def tag (program : Program n m) (state : Configuration n m) : Fin (m * 2) :=
  finProdFinEquiv (state.pc, branch program state)

/-- Reconstruction is a proof-side decoder of a recorded source tag. -/
def restore (program : Program n m) (symbol : Fin (m * 2))
    (after : Configuration n m) : Configuration n m :=
  let old := finProdFinEquiv.symm symbol
  let values := match program old.1 with
    | .inc register _ => Function.update after.counters register (after.counters register - 1)
    | .dec register _ _ =>
        if old.2 = 0 then after.counters
        else Function.update after.counters register (after.counters register + 1)
    | .halt => after.counters
  ⟨old.1, values⟩



abbrev State (n m : ℕ) := Configuration n m × ℕ

/-- An integer history code is appended to the source specification, not to native state. -/
def step (program : Program n m) (state : State n m) : Option (State n m) :=
  (Counter.step program state.1).map fun next => (next, push (tag program state.1) state.2)









end Monodromy.Counter.Recorded


/-!
## Recoverable execution histories

Finite copies of the reversed radix graph record each instruction branch.
The source registers are protected while the history is packed; the workspace
returns to zero at every dispatch. This is an intermediate reversible source
graph, prior to compression into the two native memory coordinates.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.Recording

variable {n m : ℕ}

def base (m : ℕ) : ℕ := m * 2 + 1

instance base_nonzero (m : ℕ) : NeZero (base m) := ⟨by simp [base]⟩

abbrev Node (m : ℕ) := (Fin m × Fin (Radix.size (base m))) ⊕ Fin m

def size (m : ℕ) : ℕ := m * Radix.size (base m) + m

def nodeEquiv (m : ℕ) : Node m ≃ Fin (size m) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def copy (row : Fin m) (position : Fin (Radix.size (base m))) : Fin (size m) :=
  nodeEquiv m (.inl (row, position))

def mid (row : Fin m) : Fin (size m) := nodeEquiv m (.inr row)

def dispatch (row : Fin m) : Fin (size m) := copy row (Radix.entry (base m))

def port (row : Fin m) (symbol : Fin (base m)) : Fin (size m) :=
  copy row (Radix.finish (base m) symbol)

/-- The nonzero digit retains the old address and decrement branch. -/
def digit (row : Fin m) (branch : Fin 2) : Fin (base m) :=
  ⟨(finProdFinEquiv (row, branch)).val + 1, by
    have bound := (finProdFinEquiv (row, branch)).isLt
    simp only [base]
    omega⟩

@[simp] theorem digit_eq_iff (row other : Fin m) (branch next : Fin 2) :
    digit row branch = digit other next ↔ row = other ∧ branch = next := by
  constructor
  · intro same
    have values := congrArg Fin.val same
    have tags : finProdFinEquiv (row, branch) = finProdFinEquiv (other, next) := by
      apply Fin.ext
      simp only [digit] at values
      omega
    exact Prod.mk.inj ((finProdFinEquiv).injective tags)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Precisely the active finite external arcs; halt rows contribute none. -/
def Active (program : Counter.Program n m) (pair : Fin m × Fin 3) : Prop :=
  match program pair.1 with
  | .inc _ _ => pair.2 = 0
  | .dec _ _ _ => True
  | .halt => False

instance active_decidable (program : Counter.Program n m) (pair : Fin m × Fin 3) :
    Decidable (Active program pair) := by
  unfold Active
  cases program pair.1 <;> infer_instance

abbrev Extra (program : Counter.Program n m) := {pair : Fin m × Fin 3 // Active program pair}

def historyRegister (n : ℕ) : Fin 2 → Fin (n + 2) := Fin.natAdd n

theorem historyRegister_injective (n : ℕ) : Function.Injective (historyRegister n) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd] at values
  omega

def packing (n m : ℕ) : Table (n + 2) (Radix.size (base m)) (Radix.edges (base m)) :=
  RegisterRelocation.mapTable (historyRegister n) (reverseTable (Radix.table (base m)))

theorem packing_deterministic (n m : ℕ) : Deterministic (packing n m) :=
  RegisterRelocation.deterministic _ (historyRegister_injective n) _
    (reverseTable_deterministic _ (Radix.targetCompatible (base m)))

theorem packing_targetCompatible (n m : ℕ) : TargetCompatible (packing n m) :=
  RegisterRelocation.targetCompatible _ (historyRegister_injective n) _
    (reverseTable_targetCompatible _ (Radix.deterministic (base m)))

theorem packing_no_outgoing_dispatch (index : Fin (Radix.edges (base m))) :
    (packing n m index).source ≠ Radix.entry (base m) :=
  Radix.no_incoming_entry (base m) index

theorem packing_no_incoming_port (symbol : Fin (base m))
    (index : Fin (Radix.edges (base m))) :
    (packing n m index).target ≠ Radix.finish (base m) symbol :=
  fun incoming => Radix.no_outgoing_finish (base m) symbol ⟨index, incoming⟩

def extraOrigin (program : Counter.Program n m) (arc : Extra program) : Node m :=
  match instruction : program arc.val.1 with
  | .inc _ _ => .inl (arc.val.1, Radix.entry (base m))
  | .dec _ _ _ => if arc.val.2 = 2 then .inr arc.val.1
      else .inl (arc.val.1, Radix.entry (base m))
  | .halt => False.elim (by simpa [Active, instruction] using arc.property)

def extraDestination (program : Counter.Program n m) (arc : Extra program) : Node m :=
  match instruction : program arc.val.1 with
  | .inc _ target => .inl (target, Radix.finish (base m) (digit arc.val.1 0))
  | .dec _ zero nonzero => ![
      Sum.inl (zero, Radix.finish (base m) (digit arc.val.1 0)),
      Sum.inr arc.val.1,
      Sum.inl (nonzero, Radix.finish (base m) (digit arc.val.1 1))] arc.val.2
  | .halt => False.elim (by simpa [Active, instruction] using arc.property)

def extraOperation (program : Counter.Program n m) (arc : Extra program) : Action (n + 2) :=
  match instruction : program arc.val.1 with
  | .inc register _ => .shift (Fin.castAdd 2 register) 1
  | .dec register _ _ => ![
      Action.test (Fin.castAdd 2 register) true,
      Action.test (Fin.castAdd 2 register) false,
      Action.shift (Fin.castAdd 2 register) (-1)] arc.val.2
  | .halt => False.elim (by simpa [Active, instruction] using arc.property)

def extraEdge (program : Counter.Program n m) (arc : Extra program) : Edge (n + 2) (size m) :=
  ⟨nodeEquiv m (extraOrigin program arc), nodeEquiv m (extraDestination program arc),
    extraOperation program arc⟩

abbrev Arc (program : Counter.Program n m) :=
  (Fin m × Fin (Radix.edges (base m))) ⊕ Extra program

def edges (program : Counter.Program n m) : ℕ :=
  m * Radix.edges (base m) + Fintype.card (Extra program)

def arcEquiv (program : Counter.Program n m) : Arc program ≃ Fin (edges program) :=
  (Equiv.sumCongr finProdFinEquiv (Fintype.equivFin (Extra program))).trans finSumFinEquiv

def arcEdge (program : Counter.Program n m) : Arc program → Edge (n + 2) (size m)
  | .inl (row, edge) => Glue.mapEdge (copy row) (packing n m edge)
  | .inr edge => extraEdge program edge

def table (program : Counter.Program n m) : Table (n + 2) (size m) (edges program) :=
  fun index => arcEdge program ((arcEquiv program).symm index)

@[simp] theorem table_arc (program : Counter.Program n m) (arc : Arc program) :
    table program (arcEquiv program arc) = arcEdge program arc := by
  simp [table]

/-- Every copy preserves its own finite radix address and original-row label. -/
@[simp] theorem copy_eq_iff (row other : Fin m)
    (first second : Fin (Radix.size (base m))) :
    copy row first = copy other second ↔ row = other ∧ first = second := by
  unfold copy
  rw [(nodeEquiv m).injective.eq_iff]
  simp





@[simp] theorem finish_eq_iff (first second : Fin (base m)) :
    Radix.finish (base m) first = Radix.finish (base m) second ↔ first = second := by
  unfold Radix.finish Radix.block
  rw [(Radix.nodeEquiv (base m)).injective.eq_iff]
  simp


theorem extraOrigin_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOrigin program arc = Sum.inl (arc.val.1, Radix.entry (base m)) := by
  unfold extraOrigin
  split <;> simp_all

theorem extraOrigin_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraOrigin program arc = if arc.val.2 = 2 then Sum.inr arc.val.1
      else Sum.inl (arc.val.1, Radix.entry (base m)) := by
  unfold extraOrigin
  split <;> simp_all

theorem extraDestination_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraDestination program arc =
      Sum.inl (target, Radix.finish (base m) (digit arc.val.1 0)) := by
  unfold extraDestination
  split <;> simp_all

theorem extraDestination_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraDestination program arc = ![
      Sum.inl (zero, Radix.finish (base m) (digit arc.val.1 0)),
      Sum.inr arc.val.1,
      Sum.inl (nonzero, Radix.finish (base m) (digit arc.val.1 1))] arc.val.2 := by
  unfold extraDestination
  split <;> simp_all



theorem extraOperation_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraOperation program arc = ![
      Action.test (Fin.castAdd 2 register) true,
      Action.test (Fin.castAdd 2 register) false,
      Action.shift (Fin.castAdd 2 register) (-1)] arc.val.2 := by
  unfold extraOperation
  split <;> simp_all

 theorem extraOrigin_row (program : Counter.Program n m) (arc : Extra program) :
    (extraOrigin program arc).elim Prod.fst id = arc.val.1 := by
  cases instruction : program arc.val.1 with
  | inc register target =>
      rw [extraOrigin_inc program arc register target instruction]
      rfl
  | dec register zero nonzero =>
      rw [extraOrigin_dec program arc register zero nonzero instruction]
      split_ifs <;> rfl
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim

/-- The only external dispatch alternatives are complementary tests on the same old register. -/
theorem extra_deterministic (program : Counter.Program n m) (first second : Extra program)
    (different : first ≠ second) (same : extraOrigin program first = extraOrigin program second) :
    Action.Compatible (extraOperation program first) (extraOperation program second) := by
  have rows : first.val.1 = second.val.1 := by
    have owners := congrArg (fun node : Node m => node.elim Prod.fst id) same
    simpa only [extraOrigin_row] using owners
  rcases first with ⟨⟨row, branch⟩, first_active⟩
  rcases second with ⟨⟨other, next⟩, second_active⟩
  change row = other at rows
  subst other
  cases instruction : program row with
  | inc register target =>
      have first_zero : branch = 0 := by
        have active := first_active
        unfold Active at active
        rw [instruction] at active
        exact active
      have second_zero : next = 0 := by
        have active := second_active
        unfold Active at active
        rw [instruction] at active
        exact active
      subst branch
      subst next
      exact False.elim (different (Subtype.ext rfl))
  | dec register zero nonzero =>
      rw [extraOrigin_dec program ⟨(row, branch), first_active⟩ register zero nonzero instruction,
        extraOrigin_dec program ⟨(row, next), second_active⟩ register zero nonzero instruction] at same
      rw [extraOperation_dec program ⟨(row, branch), first_active⟩ register zero nonzero instruction,
        extraOperation_dec program ⟨(row, next), second_active⟩ register zero nonzero instruction]
      fin_cases branch <;> fin_cases next <;> simp_all [Action.Compatible]
  | halt =>
      have active := first_active
      unfold Active at active
      rw [instruction] at active
      exact active.elim

/-- A nonzero history digit makes every external destination distinct. -/
theorem extraDestination_injective (program : Counter.Program n m) :
    Function.Injective (extraDestination program) := by
  intro first second same
  rcases first with ⟨⟨row, branch⟩, first_active⟩
  rcases second with ⟨⟨other, next⟩, second_active⟩
  apply Subtype.ext
  cases first_instruction : program row <;> cases second_instruction : program other
  all_goals
    have first_valid := first_active
    have second_valid := second_active
    unfold Active at first_valid second_valid
    rw [first_instruction] at first_valid
    rw [second_instruction] at second_valid
  all_goals try contradiction
  all_goals first
    | rw [extraDestination_inc program ⟨(row, branch), first_active⟩ _ _ first_instruction] at same
    | rw [extraDestination_dec program ⟨(row, branch), first_active⟩ _ _ _ first_instruction] at same
  all_goals first
    | rw [extraDestination_inc program ⟨(other, next), second_active⟩ _ _ second_instruction] at same
    | rw [extraDestination_dec program ⟨(other, next), second_active⟩ _ _ _ second_instruction] at same
  all_goals fin_cases branch <;> fin_cases next <;> simp_all

 theorem extraOrigin_shape (program : Counter.Program n m) (arc : Extra program) :
    extraOrigin program arc = Sum.inl (arc.val.1, Radix.entry (base m)) ∨
      extraOrigin program arc = Sum.inr arc.val.1 := by
  cases instruction : program arc.val.1 with
  | inc register target => exact Or.inl (extraOrigin_inc program arc register target instruction)
  | dec register zero nonzero =>
      rw [extraOrigin_dec program arc register zero nonzero instruction]
      by_cases last : arc.val.2 = 2 <;> simp [last]
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim

 theorem extraDestination_shape (program : Counter.Program n m) (arc : Extra program) :
    (∃ target symbol, extraDestination program arc =
      Sum.inl (target, Radix.finish (base m) symbol)) ∨
      extraDestination program arc = Sum.inr arc.val.1 := by
  rcases arc with ⟨⟨row, branch⟩, active⟩
  cases instruction : program row with
  | inc register target =>
      exact Or.inl ⟨target, digit row 0, extraDestination_inc program _ register target instruction⟩
  | dec register zero nonzero =>
      rw [extraDestination_dec program _ register zero nonzero instruction]
      fin_cases branch
      · exact Or.inl ⟨zero, digit row 0, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨nonzero, digit row 1, rfl⟩
  | halt =>
      have impossible := active
      unfold Active at impossible
      rw [instruction] at impossible
      exact impossible.elim

 theorem packing_extra_source_ne (program : Counter.Program n m) (row : Fin m)
    (index : Fin (Radix.edges (base m))) (arc : Extra program) :
    copy row (packing n m index).source ≠ nodeEquiv m (extraOrigin program arc) := by
  intro same
  have raw : Sum.inl (row, (packing n m index).source) = extraOrigin program arc :=
    (nodeEquiv m).injective same
  rcases extraOrigin_shape program arc with dispatch_case | mid_case
  · rw [dispatch_case] at raw
    exact packing_no_outgoing_dispatch (n := n) index (Prod.mk.inj (Sum.inl.inj raw)).2
  · rw [mid_case] at raw
    cases raw

 theorem packing_extra_target_ne (program : Counter.Program n m) (row : Fin m)
    (index : Fin (Radix.edges (base m))) (arc : Extra program) :
    copy row (packing n m index).target ≠ nodeEquiv m (extraDestination program arc) := by
  intro same
  have raw : Sum.inl (row, (packing n m index).target) = extraDestination program arc :=
    (nodeEquiv m).injective same
  rcases extraDestination_shape program arc with ⟨target, symbol, port_case⟩ | mid_case
  · rw [port_case] at raw
    exact packing_no_incoming_port (n := n) symbol index (Prod.mk.inj (Sum.inl.inj raw)).2
  · rw [mid_case] at raw
    cases raw

/-- The compiled graph chooses every enabled edge through its own finite ports. -/
theorem deterministic (program : Counter.Program n m) : Deterministic (table program) := by
  intro first second different same
  obtain ⟨first, rfl⟩ := (arcEquiv program).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv program).surjective second
  have distinct : first ≠ second := fun identical => different (congrArg (arcEquiv program) identical)
  clear different
  simp only [table_arc] at same ⊢
  rcases first with ⟨row, index⟩ | first <;> rcases second with ⟨other, next⟩ | second
  all_goals simp only [arcEdge, Glue.mapEdge, extraEdge] at same ⊢
  · rcases (copy_eq_iff row other _ _).mp same with ⟨same_rows, same_source⟩
    subst other
    exact packing_deterministic n m index next
      (fun identical => distinct (congrArg Sum.inl (Prod.ext rfl identical))) same_source
  · exact False.elim (packing_extra_source_ne program row index second same)
  · exact False.elim (packing_extra_source_ne program other next first same.symm)
  · exact extra_deterministic program first second
      (fun identical => distinct (congrArg Sum.inr identical)) ((nodeEquiv m).injective same)

/-- A unique recoverable history tag separates every external predecessor. -/
theorem targetCompatible (program : Counter.Program n m) : TargetCompatible (table program) := by
  intro first second different same
  obtain ⟨first, rfl⟩ := (arcEquiv program).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv program).surjective second
  have distinct : first ≠ second := fun identical => different (congrArg (arcEquiv program) identical)
  clear different
  simp only [table_arc] at same ⊢
  rcases first with ⟨row, index⟩ | first <;> rcases second with ⟨other, next⟩ | second
  all_goals simp only [arcEdge, Glue.mapEdge, extraEdge] at same ⊢
  · rcases (copy_eq_iff row other _ _).mp same with ⟨same_rows, same_target⟩
    subst other
    exact packing_targetCompatible n m index next
      (fun identical => distinct (congrArg Sum.inl (Prod.ext rfl identical))) same_target
  · exact False.elim (packing_extra_target_ne program row index second same)
  · exact False.elim (packing_extra_target_ne program other next first same.symm)
  · exact False.elim (distinct (congrArg Sum.inr
      (extraDestination_injective program ((nodeEquiv m).injective same))))


def frame (values : Fin n → ℕ) (history workspace : ℤ) : Fin (n + 2) → ℤ :=
  Fin.addCases (fun index => (values index : ℤ)) ![history, workspace]

def framed (control : Fin (size m)) (values : Fin n → ℕ) (history workspace : ℤ) :
    State (n + 2) (size m) := (control, frame values history workspace)

def encode (state : Counter.Configuration n m) (history : ℕ) : State (n + 2) (size m) :=
  framed (dispatch state.pc) state.counters history 0
























def embed (recorded : Counter.Recorded.State n m) : State (n + 2) (size m) :=
  encode recorded.1 recorded.2













/-! The natural domain is preserved at every intermediate port. -/

def OldNonnegative (values : Fin (n + 2) → ℤ) : Prop :=
  ∀ index : Fin n, 0 ≤ values (Fin.castAdd 2 index)

/-- Copy ports use the existing radix invariant; the decrement middle retains its positive input. -/
def admissible (program : Counter.Program n m) : Node m → (Fin (n + 2) → ℤ) → Prop
  | .inl (_, position), values =>
      Radix.Valid (base m) (position, values ∘ historyRegister n)
  | .inr row, values =>
      0 ≤ values (historyRegister n 0) ∧ values (historyRegister n 1) = 0 ∧
      match program row with
      | .dec register _ _ => 0 < values (Fin.castAdd 2 register)
      | _ => False

def Valid (program : Counter.Program n m) (state : State (n + 2) (size m)) : Prop :=
  OldNonnegative state.2 ∧ admissible program ((nodeEquiv m).symm state.1) state.2



@[simp] theorem valid_mid_iff (program : Counter.Program n m) (row : Fin m)
    (values : Fin (n + 2) → ℤ) :
    Valid program (mid row, values) ↔
      OldNonnegative values ∧ 0 ≤ values (historyRegister n 0) ∧
        values (historyRegister n 1) = 0 ∧
        match program row with
        | .dec register _ _ => 0 < values (Fin.castAdd 2 register)
        | _ => False := by
  simp only [Valid, mid, Equiv.symm_apply_apply, admissible]






























/-- A finite-control observation, independent of every counter value. -/
def Boundary (state : State (n + 2) (size m)) : Prop :=
  ∃ row : Fin m, state.1 = dispatch row

def InternalStep (program : Counter.Program n m)
    (first last : State (n + 2) (size m)) : Prop :=
  step (table program) first = some last ∧ ¬ Boundary first

abbrev InternalReaches (program : Counter.Program n m) :=
  Relation.ReflTransGen (InternalStep program)

/-- A positive run whose intermediate source states avoid all old dispatches. -/
def FirstReturn (program : Counter.Program n m)
    (first last : State (n + 2) (size m)) : Prop :=
  Boundary first ∧ Boundary last ∧
    ∃ next, step (table program) first = some next ∧ InternalReaches program next last




































def Marked (mark : Fin m → Bool) (state : State (n + 2) (size m)) : Prop :=
  ∃ row, state.1 = dispatch row ∧ mark row = true

instance (mark : Fin m → Bool) (state : State (n + 2) (size m)) : Decidable (Marked mark state) :=
  inferInstanceAs (Decidable (∃ row, state.1 = dispatch row ∧ mark row = true))





def InternalMarkedStep (program : Counter.Program n m) (mark : Fin m → Bool)
    (first last : State (n + 2) (size m)) : Prop :=
  step (table program) first = some last ∧ ¬ Marked mark first

abbrev InternalMarkedReaches (program : Counter.Program n m) (mark : Fin m → Bool) :=
  Relation.ReflTransGen (InternalMarkedStep program mark)

def MarkedFirstReturn (program : Counter.Program n m) (mark : Fin m → Bool)
    (first last : State (n + 2) (size m)) : Prop :=
  Marked mark first ∧ Marked mark last ∧
    ∃ after, step (table program) first = some after ∧ InternalMarkedReaches program mark after last













end Monodromy.Counter.Reversible.Recording

end

/-!
## Reversible prime compression

A finite virtual register vector is encoded in prime exponents. All arithmetic
uses the same two-counter radix graph; shared ports select and restore tests.
Exact first returns preserve the entire source configuration. Ordinary traces
are derived from that stronger execution statement.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PrimeCompression

variable {n q e : ℕ}

def HasSource (source : Table n q e) (position : Fin q) : Prop :=
  ∃ edge : Fin e, (source edge).source = position

instance (source : Table n q e) (position : Fin q) : Decidable (HasSource source position) :=
  inferInstanceAs (Decidable (∃ edge : Fin e, (source edge).source = position))

def HasRestore (source : Table n q e) (position : Fin q) : Prop :=
  ∃ edge : Fin e, (source edge).target = position ∧
    ∃ register : Fin n, ∃ atZero : Bool, (source edge).action = .test register atZero

instance (source : Table n q e) (position : Fin q) : Decidable (HasRestore source position) :=
  inferInstanceAs (Decidable (∃ edge : Fin e, (source edge).target = position ∧
    ∃ register : Fin n, ∃ atZero : Bool, (source edge).action = .test register atZero))

abbrev SourceSite (source : Table n q e) := {position : Fin q // HasSource source position}
abbrev RestoreSite (source : Table n q e) := {position : Fin q // HasRestore source position}
abbrev HaltSite (source : Table n q e) := {position : Fin q // ¬ HasSource source position}

def sourceEdge (source : Table n q e) (site : SourceSite source) : Fin e :=
  Fin.find (fun edge => (source edge).source = site.val) site.property

theorem sourceEdge_spec (source : Table n q e) (site : SourceSite source) :
    (source (sourceEdge source site)).source = site.val := Fin.find_spec site.property

def restoreEdge (source : Table n q e) (site : RestoreSite source) : Fin e :=
  Fin.find (fun edge => (source edge).target = site.val ∧
    ∃ register : Fin n, ∃ atZero : Bool, (source edge).action = .test register atZero) site.property

theorem restoreEdge_spec (source : Table n q e) (site : RestoreSite source) :
    (source (restoreEdge source site)).target = site.val ∧
      ∃ register : Fin n, ∃ atZero : Bool,
        (source (restoreEdge source site)).action = .test register atZero :=
  Fin.find_spec site.property

def actionRegister : Action n → Fin n
  | .shift register _ => register
  | .test register _ => register

abbrev Module (source : Table n q e) := SourceSite source ⊕ RestoreSite source

def moduleRegister (source : Table n q e) : Module source → Fin n
  | .inl site => actionRegister (source (sourceEdge source site)).action
  | .inr site => actionRegister (source (restoreEdge source site)).action

def modulus (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source) : ℕ :=
  basis.prime (moduleRegister source block)

instance (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source) :
    NeZero (modulus basis source block) := ⟨(basis.isPrime _).ne_zero⟩

def reversed (source : Table n q e) : Module source → Bool
  | .inl site => match (source (sourceEdge source site)).action with
      | .shift _ amount => decide (amount = 1)
      | .test _ _ => false
  | .inr _ => true

def componentTable (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source) :
    Table 2 (Radix.size (modulus basis source block)) (Radix.edges (modulus basis source block)) :=
  if reversed source block then reverseTable (Radix.table (modulus basis source block))
  else Radix.table (modulus basis source block)

theorem component_deterministic (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) : Deterministic (componentTable basis source block) := by
  unfold componentTable
  split
  · exact reverseTable_deterministic _ (Radix.targetCompatible _)
  · exact Radix.deterministic _

theorem component_targetCompatible (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) : TargetCompatible (componentTable basis source block) := by
  unfold componentTable
  split
  · exact reverseTable_targetCompatible _ (Radix.deterministic _)
  · exact Radix.targetCompatible _

abbrev RawPart (basis : PrimeCode.Basis n) (source : Table n q e) :=
  Σ block : Module source, Fin (Radix.size (modulus basis source block))

abbrev RawNode (basis : PrimeCode.Basis n) (source : Table n q e) :=
  HaltSite source ⊕ RawPart basis source

abbrev RawArc (basis : PrimeCode.Basis n) (source : Table n q e) :=
  Σ block : Module source, Fin (Radix.edges (modulus basis source block))

def rawSize (basis : PrimeCode.Basis n) (source : Table n q e) : ℕ :=
  Fintype.card (RawNode basis source)

def rawEdges (basis : PrimeCode.Basis n) (source : Table n q e) : ℕ :=
  Fintype.card (RawArc basis source)

def rawNodeEquiv (basis : PrimeCode.Basis n) (source : Table n q e) :
    RawNode basis source ≃ Fin (rawSize basis source) := Fintype.equivFin _

def rawArcEquiv (basis : PrimeCode.Basis n) (source : Table n q e) :
    RawArc basis source ≃ Fin (rawEdges basis source) := Fintype.equivFin _

def moduleNode (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source)
    (position : Fin (Radix.size (modulus basis source block))) : Fin (rawSize basis source) :=
  rawNodeEquiv basis source (.inr ⟨block, position⟩)

def haltNode (basis : PrimeCode.Basis n) (source : Table n q e) (site : HaltSite source) :
    Fin (rawSize basis source) := rawNodeEquiv basis source (.inl site)

theorem moduleNode_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (fun point : RawPart basis source => moduleNode basis source point.1 point.2) :=
  (rawNodeEquiv basis source).injective.comp Sum.inr_injective

theorem haltNode_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (haltNode basis source) :=
  (rawNodeEquiv basis source).injective.comp Sum.inl_injective

theorem haltNode_ne_moduleNode (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : HaltSite source) (block : Module source)
    (position : Fin (Radix.size (modulus basis source block))) :
    haltNode basis source site ≠ moduleNode basis source block position := by
  intro same
  have impossible := (rawNodeEquiv basis source).injective same
  cases impossible

def rawEdge (basis : PrimeCode.Basis n) (source : Table n q e) (arc : RawArc basis source) :
    Edge 2 (rawSize basis source) :=
  Glue.mapEdge (moduleNode basis source arc.1) (componentTable basis source arc.1 arc.2)

def rawTable (basis : PrimeCode.Basis n) (source : Table n q e) :
    Table 2 (rawSize basis source) (rawEdges basis source) :=
  fun index => rawEdge basis source ((rawArcEquiv basis source).symm index)

@[simp] theorem rawTable_arc (basis : PrimeCode.Basis n) (source : Table n q e)
    (arc : RawArc basis source) :
    rawTable basis source (rawArcEquiv basis source arc) = rawEdge basis source arc := by
  simp [rawTable]

theorem raw_deterministic (basis : PrimeCode.Basis n) (source : Table n q e) :
    Deterministic (rawTable basis source) := by
  intro first second different same
  obtain ⟨⟨left, first⟩, rfl⟩ := (rawArcEquiv basis source).surjective first
  obtain ⟨⟨right, second⟩, rfl⟩ := (rawArcEquiv basis source).surjective second
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same ⊢
  have pairs : (⟨left, (componentTable basis source left first).source⟩ : RawPart basis source) =
      ⟨right, (componentTable basis source right second).source⟩ :=
    moduleNode_injective basis source same
  have blocks : left = right := congrArg Sigma.fst pairs
  subst right
  have positions : (componentTable basis source left first).source =
      (componentTable basis source left second).source := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs
  exact component_deterministic basis source left first second
    (fun equal => different (by subst second; rfl)) positions

theorem raw_targetCompatible (basis : PrimeCode.Basis n) (source : Table n q e) :
    TargetCompatible (rawTable basis source) := by
  intro first second different same
  obtain ⟨⟨left, first⟩, rfl⟩ := (rawArcEquiv basis source).surjective first
  obtain ⟨⟨right, second⟩, rfl⟩ := (rawArcEquiv basis source).surjective second
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same ⊢
  have pairs : (⟨left, (componentTable basis source left first).target⟩ : RawPart basis source) =
      ⟨right, (componentTable basis source right second).target⟩ :=
    moduleNode_injective basis source same
  have blocks : left = right := congrArg Sigma.fst pairs
  subst right
  have positions : (componentTable basis source left first).target =
      (componentTable basis source left second).target := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs
  exact component_targetCompatible basis source left first second
    (fun equal => different (by subst second; rfl)) positions

/-- A live source address is the actual input port of its sole source module. -/
def sourceInputPosition (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) : Fin (Radix.size (modulus basis source (.inl site))) :=
  if reversed source (.inl site) then Radix.finish _ 0 else Radix.entry _

def sourceInput (basis : PrimeCode.Basis n) (source : Table n q e) (site : SourceSite source) :
    Fin (rawSize basis source) :=
  moduleNode basis source (.inl site) (sourceInputPosition basis source site)

/-- Only shift modules use this single output; test modules use their actual remainder port. -/
def sourceShiftOutput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) : Fin (rawSize basis source) :=
  moduleNode basis source (.inl site)
    (if reversed source (.inl site) then Radix.entry _ else Radix.finish _ 0)

def restoreInput (basis : PrimeCode.Basis n) (source : Table n q e) (site : RestoreSite source)
    (remainder : Fin (modulus basis source (.inr site))) : Fin (rawSize basis source) :=
  moduleNode basis source (.inr site) (Radix.finish _ remainder)

def restoreOutput (basis : PrimeCode.Basis n) (source : Table n q e) (site : RestoreSite source) :
    Fin (rawSize basis source) :=
  moduleNode basis source (.inr site) (Radix.entry _)

/-- Source boundaries are existing input ports; a stopped address is a bare vertex. -/
def boundary (basis : PrimeCode.Basis n) (source : Table n q e) (position : Fin q) :
    Fin (rawSize basis source) :=
  if active : HasSource source position then sourceInput basis source ⟨position, active⟩
  else haltNode basis source ⟨position, active⟩





theorem sourceInput_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (sourceInput basis source) := by
  intro first second same
  have pairs : (⟨Sum.inl first, sourceInputPosition basis source first⟩ : RawPart basis source) =
      ⟨Sum.inl second, sourceInputPosition basis source second⟩ :=
    moduleNode_injective basis source same
  have modules : Sum.inl first = (Sum.inl second : Module source) := congrArg Sigma.fst pairs
  exact Sum.inl.inj modules

theorem boundary_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (boundary basis source) := by
  intro first second same
  by_cases left : HasSource source first
  · by_cases right : HasSource source second
    · simp only [boundary, dite_eq_left left, dite_eq_left right] at same
      exact congrArg Subtype.val (sourceInput_injective basis source same)
    · simp only [boundary, dite_eq_left left, dite_eq_right right, sourceInput] at same
      exact False.elim (haltNode_ne_moduleNode basis source ⟨second, right⟩ _ _ same.symm)
  · by_cases right : HasSource source second
    · simp only [boundary, dite_eq_right left, dite_eq_left right, sourceInput] at same
      exact False.elim (haltNode_ne_moduleNode basis source ⟨first, left⟩ _ _ same)
    · simp only [boundary, dite_eq_right left, dite_eq_right right] at same
      exact congrArg Subtype.val (haltNode_injective basis source same)

theorem component_no_incoming_sourceInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (index : Fin (Radix.edges (modulus basis source (.inl site)))) :
    (componentTable basis source (.inl site) index).target ≠ sourceInputPosition basis source site := by
  unfold componentTable sourceInputPosition
  split_ifs
  · exact fun same => Radix.no_outgoing_finish _ 0 ⟨index, same⟩
  · exact Radix.no_incoming_entry _ index

/-- No original edge enters a source boundary; only static port identification can enter it. -/
theorem raw_no_incoming_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (position : Fin q) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).target ≠ boundary basis source position := by
  intro same
  obtain ⟨⟨block, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same
  by_cases active : HasSource source position
  · simp only [boundary, dite_eq_left active, sourceInput] at same
    have pairs : (⟨block, (componentTable basis source block index).target⟩ : RawPart basis source) =
        ⟨Sum.inl ⟨position, active⟩, sourceInputPosition basis source ⟨position, active⟩⟩ :=
      moduleNode_injective basis source same
    have blocks : block = Sum.inl ⟨position, active⟩ := congrArg Sigma.fst pairs
    subst block
    have ports : (componentTable basis source (.inl ⟨position, active⟩) index).target =
        sourceInputPosition basis source ⟨position, active⟩ := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs
    exact component_no_incoming_sourceInput basis source ⟨position, active⟩ index ports
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨position, active⟩ _ _ same.symm

/-- Module labels are preserved before the ports are identified. -/
theorem moduleNode_module (basis : PrimeCode.Basis n) (source : Table n q e)
    {first last : Module source}
    {initial : Fin (Radix.size (modulus basis source first))}
    {final : Fin (Radix.size (modulus basis source last))}
    (same : moduleNode basis source first initial = moduleNode basis source last final) :
    first = last := by
  have pairs : (⟨first, initial⟩ : RawPart basis source) = ⟨last, final⟩ :=
    moduleNode_injective basis source same
  exact congrArg Sigma.fst pairs

/-- Positions in one disjoint module retain their ordinary finite equality. -/
theorem moduleNode_position (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source)
    {first last : Fin (Radix.size (modulus basis source block))}
    (same : moduleNode basis source block first = moduleNode basis source block last) :
    first = last := by
  have pairs : (⟨block, first⟩ : RawPart basis source) = ⟨block, last⟩ :=
    moduleNode_injective basis source same
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs

/-- A local exit has no outgoing edge in the entire disjoint family. -/
theorem raw_no_outgoing_moduleNode (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) (position : Fin (Radix.size (modulus basis source block)))
    (no_outgoing : ∀ index, (componentTable basis source block index).source ≠ position)
    (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ moduleNode basis source block position := by
  intro same
  obtain ⟨⟨other, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same
  have blocks := moduleNode_module basis source same
  subst other
  exact no_outgoing index (moduleNode_position basis source block same)

/-- A local input has no incoming edge in the entire disjoint family. -/
theorem raw_no_incoming_moduleNode (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) (position : Fin (Radix.size (modulus basis source block)))
    (no_incoming : ∀ index, (componentTable basis source block index).target ≠ position)
    (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).target ≠ moduleNode basis source block position := by
  intro same
  obtain ⟨⟨other, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same
  have blocks := moduleNode_module basis source same
  subst other
  exact no_incoming index (moduleNode_position basis source block same)

/-- The source shift's selected exit is an exit in either orientation. -/
theorem raw_no_outgoing_sourceShiftOutput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ sourceShiftOutput basis source site := by
  apply raw_no_outgoing_moduleNode
  intro localIndex
  unfold componentTable
  split_ifs with backwards
  · simpa only [sourceShiftOutput, backwards, reduceIte, reverseTable, reverseEdge] using
      Radix.no_incoming_entry (modulus basis source (.inl site)) localIndex
  · simpa only [sourceShiftOutput, backwards, reduceIte] using
      (fun same => Radix.no_outgoing_finish (modulus basis source (.inl site)) 0 ⟨localIndex, same⟩)

/-- A forward query's actual remainder exits have no outgoing edge. -/
theorem raw_no_outgoing_sourceFinish (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (remainder : Fin (modulus basis source (.inl site)))
    (forward : reversed source (.inl site) = false) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠
      moduleNode basis source (.inl site) (Radix.finish _ remainder) := by
  apply raw_no_outgoing_moduleNode
  intro localIndex
  simpa only [componentTable, forward, Bool.false_eq_true, reduceIte] using
    (fun same => Radix.no_outgoing_finish (modulus basis source (.inl site)) remainder ⟨localIndex, same⟩)

theorem raw_no_outgoing_restoreOutput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ restoreOutput basis source site := by
  apply raw_no_outgoing_moduleNode
  intro localIndex
  exact Radix.no_incoming_entry (modulus basis source (.inr site)) localIndex

theorem raw_no_incoming_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (remainder : Fin (modulus basis source (.inr site)))
    (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).target ≠ restoreInput basis source site remainder := by
  apply raw_no_incoming_moduleNode
  intro localIndex
  exact fun same => Radix.no_outgoing_finish (modulus basis source (.inr site)) remainder
    ⟨localIndex, same⟩

theorem radix_entry_ne_finish (p : ℕ) (remainder : Fin p) :
    Radix.entry p ≠ Radix.finish p remainder := by
  intro same
  cases (Radix.nodeEquiv p).injective same

/-- A source-module point can meet a boundary only at its own source input. -/
theorem sourceNode_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (position : Fin (Radix.size (modulus basis source (.inl site))))
    (different : position ≠ sourceInputPosition basis source site) (target : Fin q) :
    moduleNode basis source (.inl site) position ≠ boundary basis source target := by
  intro same
  by_cases active : HasSource source target
  · simp only [boundary, dite_eq_left active] at same
    have sites : site = (⟨target, active⟩ : SourceSite source) :=
      Sum.inl.inj (moduleNode_module basis source same)
    have aligned := same.trans (congrArg (sourceInput basis source) sites).symm
    exact different (moduleNode_position basis source (.inl site) aligned)
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨target, active⟩ _ _ same.symm

theorem sourceShiftOutput_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (target : Fin q) :
    sourceShiftOutput basis source site ≠ boundary basis source target := by
  apply sourceNode_ne_boundary
  intro same
  unfold sourceInputPosition at same
  split_ifs at same
  · exact radix_entry_ne_finish _ 0 same
  · exact radix_entry_ne_finish _ 0 same.symm

theorem sourceFinish_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (remainder : Fin (modulus basis source (.inl site)))
    (forward : reversed source (.inl site) = false) (target : Fin q) :
    moduleNode basis source (.inl site) (Radix.finish _ remainder) ≠ boundary basis source target := by
  apply sourceNode_ne_boundary
  intro same
  simp only [sourceInputPosition, forward, Bool.false_eq_true, reduceIte] at same
  exact radix_entry_ne_finish _ remainder same.symm

theorem restoreOutput_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (target : Fin q) :
    restoreOutput basis source site ≠ boundary basis source target := by
  intro same
  by_cases active : HasSource source target
  · simp only [boundary, dite_eq_left active] at same
    cases moduleNode_module basis source same
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨target, active⟩ _ _ same.symm

theorem sourceNode_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (position : Fin (Radix.size (modulus basis source (.inl first))))
    (last : RestoreSite source) (remainder : Fin (modulus basis source (.inr last))) :
    moduleNode basis source (.inl first) position ≠ restoreInput basis source last remainder := by
  intro same
  cases moduleNode_module basis source same

theorem sourceShiftOutput_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (last : RestoreSite source)
    (remainder : Fin (modulus basis source (.inr last))) :
    sourceShiftOutput basis source first ≠ restoreInput basis source last remainder :=
  sourceNode_ne_restoreInput basis source first _ last remainder

theorem sourceFinish_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (initial : Fin (modulus basis source (.inl first)))
    (last : RestoreSite source) (remainder : Fin (modulus basis source (.inr last))) :
    moduleNode basis source (.inl first) (Radix.finish _ initial) ≠ restoreInput basis source last remainder :=
  sourceNode_ne_restoreInput basis source first _ last remainder

theorem restoreOutput_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first last : RestoreSite source) (remainder : Fin (modulus basis source (.inr last))) :
    restoreOutput basis source first ≠ restoreInput basis source last remainder := by
  intro same
  have sites : first = last := Sum.inr.inj (moduleNode_module basis source same)
  subst first
  exact radix_entry_ne_finish _ remainder (moduleNode_position basis source (.inr last) same)

/-- An unconditional edge has no different edge at the same compatible owner. -/
theorem shift_owner_unique (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    {first second : Fin e} {register : Fin n} {amount : ℤ}
    (shift : (table first).action = .shift register amount)
    (same : owner first = owner second) : first = second := by
  by_contra different
  have impossible := compatible first second different same
  rw [shift] at impossible
  cases (table second).action <;> exact impossible

/-- Different tests at a common compatible owner use the same register and opposite guards. -/
theorem test_owner_alternative (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    {first second : Fin e} {register : Fin n} {atZero : Bool}
    (test : (table first).action = .test register atZero)
    (different : first ≠ second) (same : owner first = owner second) :
    (table second).action = .test register (!atZero) := by
  have alternatives := compatible first second different same
  rw [test] at alternatives
  cases result : (table second).action with
  | shift => simp [result, Action.Compatible] at alternatives
  | test other flag =>
      rw [result] at alternatives
      rcases alternatives with ⟨rfl, different_flags⟩
      cases atZero <;> cases flag <;> simp_all

/-- One test fixes the register of every edge at the same compatible owner. -/
theorem test_owner_form (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    {first second : Fin e} {register : Fin n} {atZero : Bool}
    (test : (table first).action = .test register atZero)
    (same : owner first = owner second) :
    ∃ flag, (table second).action = .test register flag := by
  by_cases equal : first = second
  · subst second
    exact ⟨atZero, test⟩
  · exact ⟨!atZero, test_owner_alternative table owner compatible test equal same⟩



/-- The residue port selects zero exactly when the represented exponent is zero. -/
def testSelected (table : Table n q e) (register : Fin n) (remainder : ℕ) (edge : Fin e) : Bool :=
  decide ((table edge).action = .test register (decide (remainder ≠ 0)))

@[simp] theorem testSelected_iff (table : Table n q e) (register : Fin n) (remainder : ℕ)
    (edge : Fin e) :
    testSelected table register remainder edge = true ↔
      (table edge).action = .test register (decide (remainder ≠ 0)) := by
  simp [testSelected]

/-- One reached residue chooses at most one test at each compatible owner. -/
theorem test_matching (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    (register : Fin n) (remainder : ℕ) :
    ReversiblePorts.Matching owner (testSelected table register remainder) := by
  intro first second first_selected second_selected same
  by_contra different
  have alternatives := compatible first second different same
  rw [(testSelected_iff table register remainder first).mp first_selected,
    (testSelected_iff table register remainder second).mp second_selected] at alternatives
  exact alternatives.2 rfl

theorem source_test_matching (table : Table n q e) (deterministic : Deterministic table)
    (register : Fin n) (remainder : ℕ) :
    ReversiblePorts.Matching (fun edge => (table edge).source)
      (testSelected table register remainder) :=
  test_matching table (fun edge => (table edge).source) deterministic register remainder

theorem target_test_matching (table : Table n q e) (compatible : TargetCompatible table)
    (register : Fin n) (remainder : ℕ) :
    ReversiblePorts.Matching (fun edge => (table edge).target)
      (testSelected table register remainder) :=
  test_matching table (fun edge => (table edge).target) compatible register remainder







/-- A unit shift leaves its radix module at the original target address. -/
def ShiftConnection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ∃ site : SourceSite source,
    (source (sourceEdge source site)).action.IsShift ∧
    exit = sourceShiftOutput basis source site ∧
    entry = boundary basis source (source (sourceEdge source site)).target

/-- Restoring a tested code ends at the target's existing execution boundary. -/
def RestoreConnection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ∃ site : RestoreSite source,
    exit = restoreOutput basis source site ∧ entry = boundary basis source site.val

/-- A reached remainder port chooses a static source edge and its restoration port. -/
def TestConnection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ∃ first : SourceSite source, ∃ last : RestoreSite source,
    ∃ remainder : Fin (modulus basis source (.inl first)),
    ∃ restored : Fin (modulus basis source (.inr last)), ∃ edge : Fin e,
      (source edge).source = first.val ∧ (source edge).target = last.val ∧
      testSelected source (moduleRegister source (.inl first)) remainder.val edge = true ∧
      moduleRegister source (.inl first) = moduleRegister source (.inr last) ∧
      remainder.val = restored.val ∧
      exit = moduleNode basis source (.inl first) (Radix.finish _ remainder) ∧
      entry = restoreInput basis source last restored

/-- The entire connection relation is finite program data. -/
def Connection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ShiftConnection basis source exit entry ∨
    RestoreConnection basis source exit entry ∨ TestConnection basis source exit entry

instance (basis : PrimeCode.Basis n) (source : Table n q e) :
    DecidableRel (Connection basis source) := by
  intro exit entry
  unfold Connection ShiftConnection RestoreConnection TestConnection
  infer_instance

 theorem sourceShiftOutput_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (sourceShiftOutput basis source) := by
  intro first last same
  exact Sum.inl.inj (moduleNode_module basis source same)

 theorem restoreOutput_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (restoreOutput basis source) := by
  intro first last same
  exact Sum.inr.inj (moduleNode_module basis source same)

 theorem source_restore_disjoint (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (last : RestoreSite source)
    (initial : Fin (Radix.size (modulus basis source (.inl first))))
    (final : Fin (Radix.size (modulus basis source (.inr last)))) :
    moduleNode basis source (.inl first) initial ≠ moduleNode basis source (.inr last) final := by
  intro same
  cases moduleNode_module basis source same

 theorem selected_source_form (source : Table n q e) (deterministic : Deterministic source)
    (site : SourceSite source) (remainder : ℕ) (edge : Fin e)
    (same : (source edge).source = site.val)
    (chosen : testSelected source (moduleRegister source (.inl site)) remainder edge = true) :
    ∃ flag, (source (sourceEdge source site)).action =
      .test (moduleRegister source (.inl site)) flag := by
  exact test_owner_form source (fun index => (source index).source) deterministic
    ((testSelected_iff source _ _ edge).mp chosen)
    (same.trans (sourceEdge_spec source site).symm)

 theorem shift_test_disjoint (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit first last : Fin (rawSize basis source)}
    (shift : ShiftConnection basis source exit first)
    (test : TestConnection basis source exit last) : False := by
  obtain ⟨site, is_shift, exit_shift, _⟩ := shift
  obtain ⟨start, finish, remainder, restored, edge, same_source, _, selected, _, _, exit_test, _⟩ := test
  have modules : (Sum.inl site : Module source) = Sum.inl start :=
    moduleNode_module basis source (exit_shift.symm.trans exit_test)
  have sites : site = start := Sum.inl.inj modules
  subst start
  obtain ⟨flag, form⟩ := selected_source_form source deterministic site remainder.val edge same_source selected
  rw [form] at is_shift
  exact is_shift

 theorem test_connection_functional (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit first last : Fin (rawSize basis source)}
    (left : TestConnection basis source exit first)
    (right : TestConnection basis source exit last) : first = last := by
  obtain ⟨left_site, left_target, left_r, left_s, left_edge, left_src, left_dst,
    left_selected, _, left_values, left_exit, left_entry⟩ := left
  obtain ⟨right_site, right_target, right_r, right_s, right_edge, right_src, right_dst,
    right_selected, _, right_values, right_exit, right_entry⟩ := right
  have sites : left_site = right_site := Sum.inl.inj
    (moduleNode_module basis source (left_exit.symm.trans right_exit))
  subst right_site
  have finishes := moduleNode_position basis source (.inl left_site)
    (left_exit.symm.trans right_exit)
  have residues : left_r = right_r := by
    have pair := (Radix.nodeEquiv _).injective finishes
    simpa only [Sum.inr.injEq, Prod.mk.injEq, and_true] using pair
  subst right_r
  have edges : left_edge = right_edge := source_test_matching source deterministic
    (moduleRegister source (.inl left_site)) left_r.val
    left_edge right_edge left_selected right_selected (left_src.trans right_src.symm)
  subst right_edge
  have targets : left_target = right_target := Subtype.ext (left_dst.symm.trans right_dst)
  subst right_target
  have restored : left_s = right_s := Fin.ext (left_values.symm.trans right_values)
  subst right_s
  exact left_entry.trans right_entry.symm

/-- Each existing exit is identified with at most one existing entry. -/
theorem connection_functional (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit first last : Fin (rawSize basis source)}
    (left : Connection basis source exit first)
    (right : Connection basis source exit last) : first = last := by
  rcases left with left | left | left <;> rcases right with right | right | right
  · obtain ⟨left_site, _, left_exit, left_entry⟩ := left
    obtain ⟨right_site, _, right_exit, right_entry⟩ := right
    have same := sourceShiftOutput_injective basis source (left_exit.symm.trans right_exit)
    subst right_site
    exact left_entry.trans right_entry.symm
  · obtain ⟨left_site, _, left_exit, _⟩ := left
    obtain ⟨right_site, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source left_site right_site _ _
      (left_exit.symm.trans right_exit))
  · exact False.elim (shift_test_disjoint basis source deterministic left right)
  · obtain ⟨left_site, left_exit, _⟩ := left
    obtain ⟨right_site, _, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source right_site left_site _ _
      (right_exit.symm.trans left_exit))
  · obtain ⟨left_site, left_exit, left_entry⟩ := left
    obtain ⟨right_site, right_exit, right_entry⟩ := right
    have same := restoreOutput_injective basis source (left_exit.symm.trans right_exit)
    subst right_site
    exact left_entry.trans right_entry.symm
  · obtain ⟨left_site, left_exit, _⟩ := left
    obtain ⟨right_site, _, right_r, _, _, _, _, _, _, _, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source right_site left_site _ _
      (right_exit.symm.trans left_exit))
  · exact False.elim (shift_test_disjoint basis source deterministic right left)
  · obtain ⟨left_site, _, left_r, _, _, _, _, _, _, _, left_exit, _⟩ := left
    obtain ⟨right_site, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source left_site right_site _ _
      (left_exit.symm.trans right_exit))
  · exact test_connection_functional basis source deterministic left right

 theorem boundary_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (position : Fin q) (site : RestoreSite source)
    (remainder : Fin (modulus basis source (.inr site))) :
    boundary basis source position ≠ restoreInput basis source site remainder := by
  intro same
  by_cases active : HasSource source position
  · simp only [boundary, dite_eq_left active, sourceInput, restoreInput] at same
    cases moduleNode_module basis source same
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨position, active⟩ _ _ same

 theorem shift_connection_backward (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (left : ShiftConnection basis source first entry)
    (right : ShiftConnection basis source last entry) : first = last := by
  obtain ⟨left_site, left_shift, left_exit, left_entry⟩ := left
  obtain ⟨right_site, _, right_exit, right_entry⟩ := right
  have targets := boundary_injective basis source (left_entry.symm.trans right_entry)
  have edges : sourceEdge source left_site = sourceEdge source right_site := by
    cases action : (source (sourceEdge source left_site)).action with
    | test => simp [action, Action.IsShift] at left_shift
    | shift register amount =>
        exact shift_owner_unique source (fun edge => (source edge).target) compatible action targets
  have sites : left_site = right_site := Subtype.ext (by
    calc
      left_site.val = (source (sourceEdge source left_site)).source :=
        (sourceEdge_spec source left_site).symm
      _ = (source (sourceEdge source right_site)).source := congrArg (fun edge => (source edge).source) edges
      _ = right_site.val := sourceEdge_spec source right_site)
  subst right_site
  exact left_exit.trans right_exit.symm

 theorem shift_restore_disjoint (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (shift : ShiftConnection basis source first entry)
    (restore : RestoreConnection basis source last entry) : False := by
  obtain ⟨left, is_shift, _, left_entry⟩ := shift
  obtain ⟨right, _, right_entry⟩ := restore
  have targets := boundary_injective basis source (left_entry.symm.trans right_entry)
  obtain ⟨register, atZero, test⟩ := (restoreEdge_spec source right).2
  obtain ⟨flag, form⟩ := test_owner_form source (fun edge => (source edge).target) compatible test
    ((restoreEdge_spec source right).1.trans targets.symm)
  rw [form] at is_shift
  exact is_shift

 theorem test_connection_backward (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (left : TestConnection basis source first entry)
    (right : TestConnection basis source last entry) : first = last := by
  obtain ⟨left_site, left_target, left_r, left_s, left_edge, left_src, left_dst,
    left_selected, left_registers, left_values, left_exit, left_entry⟩ := left
  obtain ⟨right_site, right_target, right_r, right_s, right_edge, right_src, right_dst,
    right_selected, right_registers, right_values, right_exit, right_entry⟩ := right
  have targets : left_target = right_target := Sum.inr.inj
    (moduleNode_module basis source (left_entry.symm.trans right_entry))
  subst right_target
  have finishes := moduleNode_position basis source (.inr left_target)
    (left_entry.symm.trans right_entry)
  have restored : left_s = right_s := by
    have pair := (Radix.nodeEquiv _).injective finishes
    simpa only [Sum.inr.injEq, Prod.mk.injEq, and_true] using pair
  subst right_s
  have residues : left_r.val = right_r.val := left_values.trans right_values.symm
  have registers : moduleRegister source (.inl left_site) = moduleRegister source (.inl right_site) :=
    left_registers.trans right_registers.symm
  have right_chosen : testSelected source (moduleRegister source (.inl left_site)) left_r.val
      right_edge = true := by
    rw [registers, residues]
    exact right_selected
  have edges : left_edge = right_edge := target_test_matching source compatible
    (moduleRegister source (.inl left_site)) left_r.val left_edge right_edge
    left_selected right_chosen (left_dst.trans right_dst.symm)
  subst right_edge
  have sources : left_site = right_site := Subtype.ext (left_src.symm.trans right_src)
  subst right_site
  have residue : left_r = right_r := Fin.ext residues
  subst right_r
  exact left_exit.trans right_exit.symm

/-- Static port wiring is injective toward each entry, including all three connection forms. -/
theorem connection_backward (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (left : Connection basis source first entry)
    (right : Connection basis source last entry) : first = last := by
  rcases left with left | left | left <;> rcases right with right | right | right
  · exact shift_connection_backward basis source compatible left right
  · exact False.elim (shift_restore_disjoint basis source compatible left right)
  · obtain ⟨site, _, _, entered⟩ := left
    obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source _ target residue
      (entered.symm.trans restored))
  · exact False.elim (shift_restore_disjoint basis source compatible right left)
  · obtain ⟨left_site, left_exit, left_entry⟩ := left
    obtain ⟨right_site, right_exit, right_entry⟩ := right
    have sites : left_site = right_site := Subtype.ext
      (boundary_injective basis source (left_entry.symm.trans right_entry))
    subst right_site
    exact left_exit.trans right_exit.symm
  · obtain ⟨site, _, entered⟩ := left
    obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source site.val target residue
      (entered.symm.trans restored))
  · obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := left
    obtain ⟨site, _, _, entered⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source _ target residue
      (entered.symm.trans restored))
  · obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := left
    obtain ⟨site, _, entered⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source site.val target residue
      (entered.symm.trans restored))
  · exact test_connection_backward basis source compatible left right

 theorem selected_forward (source : Table n q e) (deterministic : Deterministic source)
    (site : SourceSite source) (remainder : ℕ) (edge : Fin e)
    (same : (source edge).source = site.val)
    (chosen : testSelected source (moduleRegister source (.inl site)) remainder edge = true) :
    reversed source (.inl site) = false := by
  obtain ⟨flag, form⟩ := test_owner_form source (fun index => (source index).source) deterministic
    ((testSelected_iff source _ _ edge).mp chosen)
    (same.trans (sourceEdge_spec source site).symm)
  simp only [reversed, form]

/-- Only true module exits are connected; no original source is removed. -/
theorem connection_source_free (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (index : Fin (rawEdges basis source))
    (entry : Fin (rawSize basis source)) :
    ¬ Connection basis source (rawTable basis source index).source entry := by
  rintro (shift | restore | test)
  · obtain ⟨site, _, same, _⟩ := shift
    exact raw_no_outgoing_sourceShiftOutput basis source site index same
  · obtain ⟨site, same, _⟩ := restore
    exact raw_no_outgoing_restoreOutput basis source site index same
  · obtain ⟨site, _, remainder, _, edge, same_source, _, selected, _, _, same, _⟩ := test
    exact raw_no_outgoing_sourceFinish basis source site remainder
      (selected_forward source deterministic site remainder.val edge same_source selected) index same

/-- Every selected destination is an original input with no incoming edge. -/
theorem connection_target_free (basis : PrimeCode.Basis n) (source : Table n q e)
    (index : Fin (rawEdges basis source)) (exit : Fin (rawSize basis source)) :
    ¬ Connection basis source exit (rawTable basis source index).target := by
  rintro (shift | restore | test)
  · obtain ⟨site, _, _, same⟩ := shift
    exact raw_no_incoming_boundary basis source _ index same
  · obtain ⟨site, _, same⟩ := restore
    exact raw_no_incoming_boundary basis source site.val index same
  · obtain ⟨_, site, _, remainder, _, _, _, _, _, _, _, same⟩ := test
    exact raw_no_incoming_restoreInput basis source site remainder index same

/-- Original execution boundaries are retained vertices of the compressed graph. -/
theorem boundary_unconnected (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (position : Fin q)
    (entry : Fin (rawSize basis source)) :
    ¬ Connection basis source (boundary basis source position) entry := by
  rintro (shift | restore | test)
  · obtain ⟨site, _, same, _⟩ := shift
    exact sourceShiftOutput_ne_boundary basis source site position same.symm
  · obtain ⟨site, same, _⟩ := restore
    exact restoreOutput_ne_boundary basis source site position same.symm
  · obtain ⟨site, _, remainder, _, edge, same_source, _, selected, _, _, same, _⟩ := test
    exact sourceFinish_ne_boundary basis source site remainder
      (selected_forward source deterministic site remainder.val edge same_source selected)
      position same.symm

/-- Restoration entries are retained vertices, including their selected remainder. -/
theorem restoreInput_unconnected (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (remainder : Fin (modulus basis source (.inr site)))
    (entry : Fin (rawSize basis source)) :
    ¬ Connection basis source (restoreInput basis source site remainder) entry := by
  rintro (shift | restore | test)
  · obtain ⟨first, _, same, _⟩ := shift
    exact sourceShiftOutput_ne_restoreInput basis source first site remainder same.symm
  · obtain ⟨first, same, _⟩ := restore
    exact restoreOutput_ne_restoreInput basis source first site remainder same.symm
  · obtain ⟨first, _, selected, _, _, _, _, _, _, _, same, _⟩ := test
    exact sourceFinish_ne_restoreInput basis source first selected site remainder same.symm

/-- Identification has depth one: its entry is already a retained control position. -/
theorem connection_terminal (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit entry : Fin (rawSize basis source)}
    (connected : Connection basis source exit entry) (next : Fin (rawSize basis source)) :
    ¬ Connection basis source entry next := by
  rcases connected with shift | restore | test
  · obtain ⟨site, _, _, rfl⟩ := shift
    exact boundary_unconnected basis source deterministic _ next
  · obtain ⟨site, _, rfl⟩ := restore
    exact boundary_unconnected basis source deterministic site.val next
  · obtain ⟨_, site, _, remainder, _, _, _, _, _, _, _, rfl⟩ := test
    exact restoreInput_unconnected basis source site remainder next

/-- Finite port identification supplies the complete compressed execution table. -/
def wiring (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :
    PortNetwork.Wiring (rawTable basis source) :=
  PortNetwork.Wiring.ofRelation (rawTable basis source) (Connection basis source)
    (connection_functional basis source deterministic)
    (connection_backward basis source compatible)
    (connection_terminal basis source deterministic)
    (connection_source_free basis source deterministic)
    (connection_target_free basis source)

def size (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) : ℕ :=
  PortNetwork.size (wiring basis source deterministic compatible)

/-- Every edge is an existing radix edge on the same two physical counters. -/
def table (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :
    Table 2 (size basis source deterministic compatible) (rawEdges basis source) :=
  PortNetwork.table (wiring basis source deterministic compatible)

theorem deterministic (basis : PrimeCode.Basis n) (source : Table n q e)
    (source_deterministic : Deterministic source) (compatible : TargetCompatible source) :
    Deterministic (table basis source source_deterministic compatible) :=
  PortNetwork.deterministic _ (raw_deterministic basis source)

theorem targetCompatible (basis : PrimeCode.Basis n) (source : Table n q e)
    (source_deterministic : Deterministic source) (compatible : TargetCompatible source) :
    TargetCompatible (table basis source source_deterministic compatible) :=
  PortNetwork.targetCompatible _ (raw_targetCompatible basis source)



/-- The complete natural source configuration occupies two integer counters. -/
def encode (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (state : Counter.Configuration n q) : State 2 (size basis source deterministic compatible) :=
  (PortNetwork.control (wiring basis source deterministic compatible)
    (boundary basis source state.pc), ![(basis.encode state.counters : ℤ), 0])











def siteOfEdge (source : Table n q e) (edge : Fin e) : SourceSite source :=
  ⟨(source edge).source, edge, rfl⟩

def restoreOfTest (source : Table n q e) (edge : Fin e) (register : Fin n) (flag : Bool)
    (test : (source edge).action = .test register flag) : RestoreSite source :=
  ⟨(source edge).target, edge, rfl, register, flag, test⟩





































/-- Exactly the retained finite source execution boundaries. -/
def Boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (state : State 2 (size basis source deterministic compatible)) : Prop :=
  ∃ position : Fin q, state.1 = PortNetwork.control (wiring basis source deterministic compatible)
    (boundary basis source position)

/-- State relocation changes only the finite control address. -/
def MappedState (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (block : Module source)
    (state : State 2 (Radix.size (modulus basis source block))) :
    State 2 (size basis source deterministic compatible) :=
  Glue.mapState (PortNetwork.control (wiring basis source deterministic compatible))
    (Glue.mapState (moduleNode basis source block) state)

/-- The actual compiled step with an observation on its source, not a new execution rule. -/
def InternalStep (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  step (table basis source deterministic compatible) first = some last ∧
    ¬ Boundary basis source deterministic compatible first

abbrev InternalReaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :=
  Relation.ReflTransGen (InternalStep basis source deterministic compatible)

/-- A positive compiled run, with no earlier return to a source execution boundary. -/
def FirstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  Boundary basis source deterministic compatible first ∧
  Boundary basis source deterministic compatible last ∧
  ∃ next, step (table basis source deterministic compatible) first = some next ∧
    InternalReaches basis source deterministic compatible next last



























/-- Natural configurations are viewed inside the integer source state space. -/
def naturalState (state : Counter.Configuration n q) : State n q :=
  (state.pc, fun index => (state.counters index : ℤ))











def toNatural (state : State n q) : Counter.Configuration n q :=
  ⟨state.1, fun index => (state.2 index).toNat⟩









/-- A finite marked subset of the retained source-control positions. -/
def Marked (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (mark : Fin q → Bool) (state : State 2 (size basis source deterministic compatible)) : Prop :=
  ∃ position : Fin q, state.1 = PortNetwork.control (wiring basis source deterministic compatible)
    (boundary basis source position) ∧ mark position = true





def InternalMarkedStep (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  step (table basis source deterministic compatible) first = some last ∧
    ¬ Marked basis source deterministic compatible mark first

abbrev InternalMarkedReaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool) :=
  Relation.ReflTransGen (InternalMarkedStep basis source deterministic compatible mark)

def MarkedFirstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  Marked basis source deterministic compatible mark first ∧
  Marked basis source deterministic compatible mark last ∧
  ∃ next, step (table basis source deterministic compatible) first = some next ∧
    InternalMarkedReaches basis source deterministic compatible mark next last









end Monodromy.Counter.Reversible.PrimeCompression

end


/-! Finite source marks on the same native geometric word table. -/

noncomputable section

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]

/-- Only source vertices are observed; edge ports carry no source mark. -/
def markSource (mark : Fin q → Bool) (address : Fin (q + e)) : Bool :=
  match finSumFinEquiv.symm address with
  | .inl position => mark position
  | .inr _ => false



/-- The existing native words with a different finite stop table. -/
def markedProgram (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) : Program (11 * (q + e)) :=
  StagedProgram.markedCompile 11 (q + e) (stages table deterministic compatible) (markSource mark)



/-- A source return is detected by the actual finite root observation. -/
def MarkedBoundary (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (state : Memory) : Prop :=
  (markedProgram table deterministic compatible mark).haltSignal state = 1







def NativeInternalStep (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (first last : Memory) : Prop :=
  (haltingProgram table deterministic compatible).step first = some last ∧
    ¬ MarkedBoundary table deterministic compatible mark first

abbrev NativeInternalReaches (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) :=
  Relation.ReflTransGen (NativeInternalStep table deterministic compatible mark)

def NativeFirstReturn (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (first last : Memory) : Prop :=
  MarkedBoundary table deterministic compatible mark first ∧
  MarkedBoundary table deterministic compatible mark last ∧
  ∃ next, (haltingProgram table deterministic compatible).step first = some next ∧
    NativeInternalReaches table deterministic compatible mark next last













/-- Execute the original native table once, then the same words until the next finite root mark. -/
def nativeMacro (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (state : Memory) : Part (Option Memory) :=
  match (haltingProgram table deterministic compatible).step state with
  | none => Part.some none
  | some next => ((markedProgram table deterministic compatible mark).eval next).map some





end Monodromy.ReversibleCompilation

end


